// Helper for running ArduPilot with an external JSBSim simulator.
//
// The `arduplane` and `JSBSim` processes communicate over two sockets.  The
// usual startup procedure is as follows:
//
// 1. `arduplane` starts listening on UDP port 5504
// 2. `arduplane` spawns `JSBSim`
// 3. `JSBSim` sends a UDP packet on port 5504, and also starts listening on
//    TCP port 5505
// 4. `arduplane` connects to TCP port 5505
//
// We'd like to eliminate step (2) so that `JSBSim` can be run independently
// from `arduplane` (on a different machine, ideally).  However, if we start
// `arduplane` before `JSBSim`, the connection in step (4) will fail.  And if
// we start `JSBSim` before `arduplane`, the UDP send in step (3) will fail,
// and the simulation won't start up correctly.
//
// `jsbsim_proxy` provides a workaround: it listens on port 5505, and only once
// it receives an incoming connection, it spawns `JSBSim` listening on port
// 15505 and proxies traffic between the two.  This way `arduplane` has
// something to connect to in step (4), and `JSBSim` can send its initial UDP
// message in step (3).
//
// `jsbsim_proxy` doesn't do anything special with the UDP traffic; `JSBSim`
// can just send those messages to `arduplane` on the normal port.

#include <poll.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>
#include <arpa/inet.h>
#include <netinet/in.h>
#include <sys/socket.h>
#include <sys/time.h>

#define CONNECT_MAX_RETRIES 10

struct buffer {
    char* data;
    // Size of the `data` array.
    size_t cap;
    // Amount of initialized data in the array.
    size_t len;
    // Amount of data that has been sent out so far.  `0 <= pos <= len`.
    size_t pos;
};

void buffer_init(struct buffer* buf, char* data, size_t cap) {
    buf->data = data;
    buf->cap = cap;
    buf->len = 0;
    buf->pos = 0;
}

int buffer_has_pending_data(const struct buffer* buf) {
    return buf->pos < buf->len;
}

// Try to write some of the pending data on `to_fd`.  Returns 0 on success, -1
// on failure.
int buffer_write(struct buffer* buf, int to_fd) {
    if (buf->pos == buf->len) {
        return 0;
    }
    ssize_t n = write(to_fd, buf->data + buf->pos, buf->len - buf->pos);
    if (n < 0) {
        return -1;
    } else {
        buf->pos += n;
        if (buf->pos == buf->len) {
            buf->pos = 0;
            buf->len = 0;
        }
        return 0;
    }
}

// Try to read some data from `from_fd` into `buf`.  Returns 1 on success, 0 on
// EOF, and -1 on error.
int buffer_read(struct buffer* buf, int from_fd) {
    if (buf->len == buf->cap) {
        return 0;
    }
    ssize_t n = read(from_fd, buf->data + buf->len, buf->cap - buf->len);
    if (n < 0) {
        return -1;
    } else if (n == 0) {
        return 0;
    } else {
        buf->len += n;
        return 1;
    }
}

int main(int argc, char *argv[]) {
    // Declare child_pid early so we can kill the child on error if needed
    int child_pid = 0;

    int ret;

    if (argc < 2) {
        fprintf(stderr, "usage: %s JSBSim [args...]\n", argc > 0 ? argv[0] : "jsbsim_proxy");
        goto error;
    }


    // Listen and accept an incoming connection.

    int sock_listen = socket(AF_INET, SOCK_STREAM, 0);
    if (sock_listen < 0) {
        perror("socket (sock_listen)");
        goto error;
    }

    const char* bind_addr_str = getenv("JSBSIM_PROXY_BIND_ADDR");
    if (bind_addr_str == NULL) {
        bind_addr_str = "127.0.0.1";
    }
    struct sockaddr_in bind_addr = {0};
    bind_addr.sin_family = AF_INET;
    ret = inet_pton(bind_addr.sin_family, bind_addr_str, &bind_addr.sin_addr);
    if (ret == 0) {
        fprintf(stderr, "bad address in $JSBSIM_PROXY_BIND_ADDR: %s\n", bind_addr_str);
        goto error;
    } else if (ret < 0) {
        perror("inet_pton");
        goto error;
    }
    bind_addr.sin_port = htons(5505);
    ret = bind(sock_listen, (const struct sockaddr*)&bind_addr, sizeof(bind_addr));
    if (ret != 0) {
        perror("bind");
        goto error;
    }

    ret = listen(sock_listen, 1);
    if (ret != 0) {
        perror("listen");
        goto error;
    }

    fprintf(stderr, "listening on port %d...\n", ntohs(bind_addr.sin_port));
    int sock_a = accept(sock_listen, NULL, NULL);
    if (sock_a < 0) {
        perror("accept");
        goto error;
    }

    fprintf(stderr, "got incoming connection\n");


    // Spawn JSBSim

    fprintf(stderr, "starting jsbsim...\n");
    for (int i = 1; i < argc; ++i) {
        fprintf(stderr, "%s%c", argv[i], i == argc - 1 ? '\n': ' ');
    }
    // Flush in case the child process also tries to write to stderr.
    fflush(stderr);

    child_pid = fork();
    if (child_pid == 0) {
        ret = execvp(argv[1], argv + 1);
        if (ret != 0) {
            perror("execvp");
            exit(1);
        }
    }
    if (child_pid < 0) {
        perror("fork");
        goto error;
    }


    // Connect to JSBSim

    struct sockaddr_in connect_addr = {0};
    connect_addr.sin_family = AF_INET;
    connect_addr.sin_addr.s_addr = inet_addr("127.0.0.1");
    connect_addr.sin_port = htons(15505);

    struct timespec retry_delay = {0};
    // 500 ms
    retry_delay.tv_sec = 0;
    retry_delay.tv_nsec = 500 * 1000000;

    int sock_b = -1;
    for (int retry_count = 1; retry_count <= CONNECT_MAX_RETRIES; ++retry_count) {
        fprintf(stderr, "connecting to JSBSim (attempt %d)...\n", retry_count);

        // From the connect(2) manpage:
        // >  If connect() fails, consider the state of the socket as
        // > unspecified.  Portable applications should close the socket and
        // > create a new one for reconnecting.
        sock_b = socket(AF_INET, SOCK_STREAM, 0);
        if (sock_b < 0) {
            perror("socket (sock_b)");
            goto error;
        }

        ret = connect(sock_b, (const struct sockaddr*)&connect_addr, sizeof(connect_addr));
        if (ret == 0) {
            break;
        }
        if (retry_count == CONNECT_MAX_RETRIES) {
            perror("connect");
            goto error;
        }

        ret = close(sock_b);
        if (ret != 0) {
            perror("close (sock_b)");
            goto error;
        }
        sock_b = -1;

        nanosleep(&retry_delay, NULL);
    }

    fprintf(stderr, "connected to JSBSim\n");

    // Forward traffic between `sock_a` and `sock_b`.

    char ab_buf_data[128] = {0};
    struct buffer ab_buf;
    buffer_init(&ab_buf, ab_buf_data, sizeof(ab_buf_data));

    char ba_buf_data[2048] = {0};
    struct buffer ba_buf;
    buffer_init(&ba_buf, ba_buf_data, sizeof(ba_buf_data));

    struct pollfd poll_fds[2] = {0};
    poll_fds[0].fd = sock_a;
    poll_fds[1].fd = sock_b;

    for (;;) {
        poll_fds[0].events = 0;
        poll_fds[0].revents = 0;
        poll_fds[1].events = 0;
        poll_fds[1].revents = 0;

        if (buffer_has_pending_data(&ab_buf)) {
            poll_fds[1].events |= POLLOUT;
        } else {
            poll_fds[0].events |= POLLIN;
        }

        if (buffer_has_pending_data(&ba_buf)) {
            poll_fds[0].events |= POLLOUT;
        } else {
            poll_fds[1].events |= POLLIN;
        }

        ret = poll(poll_fds, 2, 0);

        if (poll_fds[0].revents & POLLOUT) {
            //fprintf(stderr, "try to write sock_a\n");
            ret = buffer_write(&ba_buf, sock_a);
            if (ret < 0) {
                perror("write (sock_a)");
                goto error;
            }
        } else if (poll_fds[0].revents != 0) {
            //fprintf(stderr, "try to read sock_a\n");
            ret = buffer_read(&ab_buf, sock_a);
            if (ret < 0) {
                perror("read (sock_a)");
                goto error;
            } else if (ret == 0) {
                fprintf(stderr, "got EOF on sock_a\n");
                break;
            }
        }

        if (poll_fds[1].revents & POLLOUT) {
            //fprintf(stderr, "try to write sock_b\n");
            ret = buffer_write(&ab_buf, sock_b);
            if (ret < 0) {
                perror("write (sock_b)");
                goto error;
            }
        } else if (poll_fds[1].revents != 0) {
            //fprintf(stderr, "try to read sock_b\n");
            ret = buffer_read(&ba_buf, sock_b);
            if (ret < 0) {
                perror("read (sock_b)");
                goto error;
            } else if (ret == 0) {
                fprintf(stderr, "got EOF on sock_b\n");
                break;
            }
        }
    }


    // Clean up.

    kill(child_pid, SIGTERM);

    return 0;

error:
    // `child_pid` may be 0 if we haven't called `fork` yet, and it may be
    // negative if `fork` failed.
    if (child_pid > 0) {
        kill(child_pid, SIGTERM);
    }
    return 1;
}
