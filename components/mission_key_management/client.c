// Client state machine.  Each connection has a separate `struct client`
// object, which tracks progress through the key request protocol for that
// connection.

#include <stdlib.h>
#include <string.h>

#include "client.h"

#ifndef CN_ENV
# include <sys/epoll.h>
# include <sys/socket.h>
# include <unistd.h>
# include <stdio.h>
#else
# include "cn_stubs.h"
#endif


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
    c->key = NULL;
    return c;
}

void client_delete(struct client* c) {
    int ret = shutdown(c->fd, SHUT_RDWR);
    if (ret != 0) {
        perror("shutdown (client_delete)");
        // Keep going.  Even if TCP shutdown fails, we still need to close the
        // file descriptor.
    }
    ret = close(c->fd);
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
            return c->key;
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
            return KEY_SIZE;
        case CS_DONE:
            return 0;

        default:
            // Unreachable
            return 0;
    }
}


int client_epoll_ctl(struct client* c, int epfd, int op) {
#ifndef CN_ENV
    struct epoll_event ev;
    ev.data.ptr = c;
    ev.events = client_state_epoll_events(c->state);
    return epoll_ctl(epfd, op, c->fd, &ev);
#else
    return 0;
#endif
}


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
        //
        // We return `RES_ERROR` here so that the epoll loop will close the
        // connection.  Since we didn't properly process the events indicated
        // by `events`, presumably some of those events are still ready and
        // will show up again the next time around the epoll loop, at which
        // point we'll fail to handle them again.  Closing the connection
        // prevents this from looping infinitely and wasting CPU.
        return RES_ERROR;
    }

    // The async operation for the current state is finished.  We can now
    // transition to the next state.
    switch (c->state) {
        case CS_RECV_KEY_ID:
            memcpy(c->challenge, "random challenge", NONCE_SIZE);
            client_change_state(c, CS_SEND_CHALLENGE);
            break;

        case CS_SEND_CHALLENGE:
            client_change_state(c, CS_RECV_RESPONSE);
            break;

        case CS_RECV_RESPONSE:
            c->key = policy_match(c->key_id, c->challenge,
                    c->response, c->response + MEASURE_SIZE);
            if (c->key == NULL) {
                // No matching key was found for this request.
                fprintf(stderr, "client %d: error: bad request for key %u\n", c->fd, c->key_id[0]);
                return RES_ERROR;
            }
            client_change_state(c, CS_SEND_KEY);
            fprintf(stderr, "client %d: sending key %u\n", c->fd, c->key_id[0]);
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
