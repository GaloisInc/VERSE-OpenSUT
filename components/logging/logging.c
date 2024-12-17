#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>
#include <stdarg.h>
#include <unistd.h>
#include <errno.h>
#include <arpa/inet.h>
#include <netinet/in.h>
#include <sys/socket.h>
#include <time.h>

#ifndef CN_ENV
// `mavlink_get_info.h` uses `offsetof`, but doesn't include the header
// `stddef.h` that provides it.  We include the header here so `offsetof` will
// be available.
# include <stddef.h>
# include <mavlink/all/mavlink.h>
# include <mavlink/mavlink_get_info.h>
#else
# include "cn_mavlink_stubs.h"
#endif

#include "output.h"


int main(int argc, char *argv[]) {
    int ret;


    // Parse host and port options

    const char* host_str = "127.0.0.1";
    if (argc >= 2) {
        host_str = argv[1];
    }

    // Default port is 5762, which is the Ardupilot SITL telemetry port.
    uint16_t port = 5762;
    if (argc >= 3) {
        const char* port_str = argv[2];
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


    // Connect to the Ardupilot telemetry port.
    //
    // Requirement 1: The logging component shall connect to the secondary
    // autopilot telemetry port....

    struct sockaddr_in connect_addr = {0};
    connect_addr.sin_family = AF_INET;
    ret = inet_aton(host_str, &connect_addr.sin_addr);
    if (ret != 1) {
        perror("inet_aton");
        return 1;
    }
    connect_addr.sin_port = htons(port);

    int sock = socket(AF_INET, SOCK_STREAM, 0);
    if (sock < 0) {
        perror("socket");
        return 1;
    }

    ret = connect(sock, (const struct sockaddr*)&connect_addr, sizeof(connect_addr));
    if (ret != 0) {
        perror("connect");
        return 1;
    }


    // Read messages from the socket and print them.
    //
    // Requirement 1.1: The logging component shall read MAVlink messages from
    // a socket.
    //
    // Requirement 1: The logging component shall ... record some or all
    // telemetry values to disk.

    char buf[4096];

    mavlink_status_t status;
    mavlink_message_t msg;
    int chan = MAVLINK_COMM_0;

    for (;;) {
        ssize_t n = read(sock, buf, sizeof(buf));
        if (n == 0) {
            // EOF - connection closed
            fprintf(stderr, "connection closed\n");
            break;
        } else if (n < 0) {
            perror("recv");
            return 1;
        }

        for (ssize_t i = 0; i < n; ++i) {
            uint8_t byte = buf[i];
            if (mavlink_parse_char(chan, byte, &msg, &status)) {
                if (msg.msgid == MAVLINK_MSG_ID_GLOBAL_POSITION_INT) {
                    handle_message(&msg);
                }
                // Other message types are ignored for now.  This reduces the
                // amount of disk I/O required when running the logger inside a
                // VM.
            }
        }
    }

    return 0;
}
