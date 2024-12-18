#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <errno.h>
#include <sys/epoll.h>
#include <arpa/inet.h>
#include <netinet/in.h>
#include <sys/socket.h>
#include "client.h"
#include "policy.h"


int main() {
    int ret;


    policy_add(
            (const uint8_t*)"\0",
            (const uint8_t*)"measurement of valid client code",
            (const uint8_t*)"key for encrypting secret things");

    policy_add(
            (const uint8_t*)"\001",
            (const uint8_t*)"measurement of valid client code",
            (const uint8_t*)"another secret cryptographic key");

    static const uint8_t test_attest_helper_measure[MEASURE_SIZE] = {
        0xd2, 0x81, 0x3a, 0x46, 0xb2, 0xa0, 0x71, 0x67,
        0x0f, 0xca, 0x30, 0x87, 0x62, 0xec, 0x34, 0xa7,
        0x6a, 0x61, 0xd6, 0x7a, 0x32, 0x1b, 0x43, 0xcb,
        0x7d, 0x25, 0x2f, 0xe4, 0xcc, 0x1d, 0x92, 0xa7
    };
    policy_add(
            (const uint8_t*)"\0",
            test_attest_helper_measure,
            (const uint8_t*)"extra key for test_attest to use");

    // Measure of `mkm_client`'s `run_client.sh` script.
    static const uint8_t mkm_client_run_measure[MEASURE_SIZE] = {
        0x5b, 0xfa, 0xa5, 0xe5, 0xed, 0xdc, 0xc3, 0x6e,
        0x15, 0x5b, 0xde, 0x85, 0x9a, 0xc5, 0x5e, 0x52,
        0x77, 0x93, 0x67, 0x91, 0x76, 0x1a, 0x34, 0xb2,
        0xc6, 0xbc, 0xb5, 0xda, 0x81, 0xb4, 0x74, 0x6b
    };
    policy_add(
            (const uint8_t*)"\0",
            mkm_client_run_measure,
            (const uint8_t*)"mkm_client uses this key to test");


    // Open the listening socket.

    int sock_listen = socket(AF_INET, SOCK_STREAM, 0);
    if (sock_listen < 0) {
        perror("socket (sock_listen)");
        return 1;
    }

    struct sockaddr_in bind_addr = {0};
    bind_addr.sin_family = AF_INET;

    const char* bind_addr_str = getenv("MKM_BIND_ADDR");
    if (bind_addr_str == NULL) {
        bind_addr_str = "127.0.0.1";
    }
    ret = inet_pton(bind_addr.sin_family, bind_addr_str, &bind_addr.sin_addr);
    if (ret == 0) {
        fprintf(stderr, "bad address in $MKM_BIND_ADDR: %s\n", bind_addr_str);
        return 1;
    } else if (ret < 0) {
        perror("inet_pton");
        return 1;
    }

    uint16_t port = 6000;
    const char* port_str = getenv("MKM_PORT");
    if (port_str != NULL) {
        char* port_str_end = NULL;
        errno = 0;
        long port_long = strtol(port_str, &port_str_end, 10);
        if (errno != 0) {
            perror("strtol");
            return 1;
        }
        if (*port_str == '\0' || *port_str_end != '\0') {
            fprintf(stderr, "invalid port number \"%s\"\n", port_str);
            return 1;
        }
        if (port_long < 0 || port_long > (long)UINT16_MAX) {
            fprintf(stderr, "port number %s is out of range", port_str);
            return 1;
        }
        port = port_long;
    }
    bind_addr.sin_port = htons(port);

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
