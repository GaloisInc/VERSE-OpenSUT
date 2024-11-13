#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <sys/epoll.h>
#include <arpa/inet.h>
#include <netinet/in.h>
#include <sys/socket.h>


#define NUM_SECRET_KEYS 2
#define SECRET_KEY_SIZE 32

static const uint8_t mission_keys[NUM_SECRET_KEYS][SECRET_KEY_SIZE] = {
    "key for encrypting secret things",
    "another secret cryptographic key"
};

enum client_state {
    // Waiting to receive a request for a specific key ID.
    CS_RECV_KEY_ID,
    // In the process of sending a challenge for attestation.
    CS_SEND_CHALLENGE,
    // Waiting to receeive the attestation response.
    CS_RECV_RESPONSE,
    // In the process of sending the key.
    CS_SEND_KEY,
    // Protocol finished - no more input or output is expected.
    CS_DONE,
};

enum client_op {
    OP_NONE,
    OP_READ,
    OP_WRITE,
};

struct client {
    int fd;
    // Buffers for async read/write operations.
    uint8_t challenge[32];
    uint8_t response[32];
    uint8_t key_id[1];
    // Read/write position within the current buffer.  Which buffer this refers
    // to depends on the current state.  For the chosen buffer, `buf[i]` is
    // initialized only within the range `0 <= i < pos`.
    uint8_t pos;
    enum client_state state;
};

uint32_t client_state_epoll_events(enum client_state state) {
    switch (state) {
        case CS_RECV_KEY_ID:
            return EPOLLIN;
        case CS_SEND_CHALLENGE:
            return EPOLLOUT;
        case CS_RECV_RESPONSE:
            return EPOLLIN;
        case CS_SEND_KEY:
            return EPOLLOUT;
        case CS_DONE:
            return 0;

        default:
            // Unreachable
            return 0;
    }
}

struct client* client_new(int fd) {
    struct client* c = malloc(sizeof(struct client));
    if (c == NULL) {
        perror("malloc (client_new)");
        return NULL;
    }
    c->fd = fd;
    c->pos = 0;
    c->state = CS_RECV_KEY_ID;
    return c;
}

// Deallocate client data.  The client should be removed from epoll before
// calling this.
void client_delete(struct client* c) {
    int ret = close(c->fd);
    if (ret != 0) {
        perror("close (client_delete)");
        // Keep going.  On Linux, `close` always closes the file descriptor,
        // but may report I/O errors afterward.
    }
    free(c);
}


uint8_t* client_read_buffer(struct client* c) {
    switch (c->state) {
        case CS_RECV_KEY_ID:
            return c->key_id;
        case CS_RECV_RESPONSE:
            return c->response;
        default:
            return NULL;
    }
}

const uint8_t* client_write_buffer(struct client* c) {
    switch (c->state) {
        case CS_SEND_CHALLENGE:
            return c->challenge;
        case CS_SEND_KEY:
            return mission_keys[c->key_id[0]];
        default:
            return NULL;
    }
}

size_t client_buffer_size(struct client* c) {
    switch (c->state) {
        case CS_RECV_KEY_ID:
            return sizeof(c->key_id);
        case CS_SEND_CHALLENGE:
            return sizeof(c->challenge);
        case CS_RECV_RESPONSE:
            return sizeof(c->response);
        case CS_SEND_KEY:
            return SECRET_KEY_SIZE;
        case CS_DONE:
            return 0;

        default:
            // Unreachable
            return 0;
    }
}


int client_epoll_ctl(struct client* c, int epfd, int op) {
    struct epoll_event ev;
    ev.data.ptr = c;
    ev.events = client_state_epoll_events(c->state);
    return epoll_ctl(epfd, op, c->fd, &ev);
}


enum client_event_result {
    RES_ERROR = -2,
    RES_EOF = -1,
    RES_PENDING = 0,
    RES_DONE = 1,
};

enum client_event_result client_read(struct client* c) {
    uint8_t* buf = client_read_buffer(c);
    if (buf == NULL) {
        // There's no read operation to perform.
        return RES_DONE;
    }

    size_t buf_size = client_buffer_size(c);
    if (c->pos >= buf_size) {
        // Read operation has already finished.
        return RES_DONE;
    }

    int ret = read(c->fd, buf + c->pos, buf_size - c->pos);
    if (ret < 0) {
        perror("read (client_read)");
        return RES_ERROR;
    } else if (ret == 0) {
        return RES_EOF;
    }
    c->pos += ret;

    return c->pos == buf_size ? RES_DONE : RES_PENDING;
}

enum client_event_result client_write(struct client* c) {
    const uint8_t* buf = client_write_buffer(c);
    if (buf == NULL) {
        // There's no write operation to perform.
        return RES_DONE;
    }

    size_t buf_size = client_buffer_size(c);
    if (c->pos >= buf_size) {
        // Write operation has already finished.
        return RES_DONE;
    }

    int ret = write(c->fd, buf + c->pos, buf_size - c->pos);
    if (ret < 0) {
        perror("write (client_write)");
        return RES_ERROR;
    } else if (ret == 0) {
        return RES_EOF;
    }
    c->pos += ret;

    return c->pos == buf_size ? RES_DONE : RES_PENDING;
}


void client_change_state(struct client* c, enum client_state new_state) {
    c->state = new_state;
    c->pos = 0;
}

enum client_event_result client_event(struct client* c, uint32_t events) {
    if (events & EPOLLIN) {
        enum client_event_result result = client_read(c);
        if (result != RES_DONE) {
            return result;
        }
    }
    if (events & EPOLLOUT) {
        enum client_event_result result = client_write(c);
        if (result != RES_DONE) {
            return result;
        }
    }

    if (c->pos < client_buffer_size(c)) {
        // Async read/write operation isn't yet finished.
        //
        // This should be unreachable.  `client_event` should only be called
        // when progress can be made on a current async read or write
        // operation, and the call to `client_read`/`client_write` above will
        // return `RES_PENDING` (causing `client_event` to return early) if the
        // operation isn't finished.
        return RES_PENDING;
    }

    // The async operation for the current state is finished.  We can now
    // transition to the next state.
    switch (c->state) {
        case CS_RECV_KEY_ID:
            memcpy(c->challenge, "This challenge is totally random", 32);
            client_change_state(c, CS_SEND_CHALLENGE);
            break;

        case CS_SEND_CHALLENGE:
            client_change_state(c, CS_RECV_RESPONSE);
            break;

        case CS_RECV_RESPONSE:
            {
                // TODO: properly validate the response
                int resp_ok = memcmp(c->challenge, c->response, 32) == 0;
                if (!resp_ok) {
                    fprintf(stderr, "client %d: error: bad response\n", c->fd);
                    return RES_ERROR;
                }
                uint8_t key_id = c->key_id[0];
                if (key_id >= NUM_SECRET_KEYS) {
                    fprintf(stderr, "client %d: error: bad request for key %u\n", c->fd, key_id);
                    return RES_ERROR;
                }
                client_change_state(c, CS_SEND_KEY);
                fprintf(stderr, "client %d: sending key %u\n", c->fd, key_id);
            }
            break;

        case CS_SEND_KEY:
            client_change_state(c, CS_DONE);
            break;

        case CS_DONE:
            // No-op.  This connection is finished, and the main loop should
            // disconnect.
            break;
    }

    return RES_DONE;
}


int main() {
    int ret;


    // Open the listening socket.

    int sock_listen = socket(AF_INET, SOCK_STREAM, 0);
    if (sock_listen < 0) {
        perror("socket (sock_listen)");
        return 1;
    }

    const char* bind_addr_str = getenv("MKM_BIND_ADDR");
    if (bind_addr_str == NULL) {
        bind_addr_str = "127.0.0.1";
    }
    struct sockaddr_in bind_addr = {0};
    bind_addr.sin_family = AF_INET;
    ret = inet_pton(bind_addr.sin_family, bind_addr_str, &bind_addr.sin_addr);
    if (ret == 0) {
        fprintf(stderr, "bad address in $MKM_BIND_ADDR: %s\n", bind_addr_str);
        return 1;
    } else if (ret < 0) {
        perror("inet_pton");
        return 1;
    }
    bind_addr.sin_port = htons(6000);
    ret = bind(sock_listen, (const struct sockaddr*)&bind_addr, sizeof(bind_addr));
    if (ret != 0) {
        perror("bind");
        return 1;
    }

    ret = listen(sock_listen, 1);
    if (ret != 0) {
        perror("listen");
        return 1;
    }
    fprintf(stderr, "listening on %s:%d...\n", bind_addr_str, ntohs(bind_addr.sin_port));


    // Set up epoll

    int epfd = epoll_create1(0);
    struct epoll_event ev = {0};
    ev.data.ptr = NULL;
    ev.events = EPOLLIN;
    ret = epoll_ctl(epfd, EPOLL_CTL_ADD, sock_listen, &ev);
    if (ret != 0) {
        perror("epoll_ctl (add sock_listen)");
        return 1;
    }

    for (;;) {
        struct epoll_event ev_buf[10] = {0};
        ret = epoll_wait(epfd, ev_buf, sizeof(ev_buf) / sizeof(ev_buf[0]), -1);
        if (ret < 0) {
            perror("epoll_wait");
            return 1;
        }

        unsigned n = ret;
        for (unsigned i = 0; i < n; ++i) {
            struct client* c = ev_buf[i].data.ptr;
            uint32_t events = ev_buf[i].events;

            fprintf(stderr, "epoll event %d: client %p, events %x\n", i, (void*)c, events);

            if (c == NULL) {
                // Listening socket is ready.
                if (events & EPOLLIN) {
                    // TODO: get peer address and log it
                    int sock_client = accept(sock_listen, NULL, 0);
                    struct client* c = client_new(sock_client);
                    ret = client_epoll_ctl(c, epfd, EPOLL_CTL_ADD);
                    if (ret != 0) {
                        perror("epoll_ctl (add)");
                        return 1;
                    }
                    // `c` is now owned by the epoll object.  We will get its
                    // pointer back when events occur on its socket.
                    fprintf(stderr, "client %d: added, state = %d\n", c->fd, c->state);
                }
                continue;
            }

            // A client socket is ready.
            enum client_event_result result = client_event(c, events);
            fprintf(stderr, "client %d: handled event, state = %d, result = %d\n",
                    c->fd, c->state, result);
            switch (result) {
                case RES_ERROR:
                case RES_EOF:
                    // Cancel this transaction.  The case below will tear down
                    // the connection.
                    c->state = CS_DONE;
                    break;
                case RES_PENDING:
                    // No-op
                    break;
                case RES_DONE:
                    // The current state's async operation finished.  We may
                    // have transitioned to a new state that expects a
                    // different set of epoll events.
                    ret = client_epoll_ctl(c, epfd, EPOLL_CTL_MOD);
                    if (ret != 0) {
                        perror("epoll_ctl (mod)");
                        return 1;
                    }
                    break;
            }

            if (c->state == CS_DONE) {
                ret = client_epoll_ctl(c, epfd, EPOLL_CTL_DEL);
                if (ret != 0) {
                    perror("epoll_ctl (del)");
                    return 1;
                }
                fprintf(stderr, "client %d: deleted\n", c->fd);
                client_delete(c);
            }
        }
    }

    // Unreachable
}
