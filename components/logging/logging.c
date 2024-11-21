#define MAVLINK_USE_MESSAGE_INFO

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



// Buffer type for building up a single line of log output.
struct buffer {
    size_t pos;
    char buf[4096];
};

void buffer_init(struct buffer* b) {
    b->pos = 0;
    b->buf[0] = '\0';
}

void buffer_printf(struct buffer* b, const char* fmt, ...) {
    va_list args;
    va_start(args, fmt);
    size_t avail = sizeof(b->buf) - b->pos;
    ssize_t ret = vsnprintf(b->buf + b->pos, avail, fmt, args);
    if (ret < 0) {
        perror("vsnprintf");
        exit(1);
    } else if ((size_t)ret > avail) {
        b->pos = sizeof(b->buf);
    } else {
        b->pos += ret;
    }
    va_end(args);
}

void buffer_strftime(struct buffer* b, const char* fmt, const struct tm* tm) {
    size_t avail = sizeof(b->buf) - b->pos;
    size_t ret = strftime(b->buf + b->pos, avail, fmt, tm);
    if (ret == 0) {
        // From `strftime(3)`: "If the length of the result string (including
        // the terminating null byte) would exceed max bytes, then strftime()
        // returns 0, and the contents of the array are undefined."  Since a
        // failing `strftime` call is allowed to remove the null terminator, we
        // restore it here.
        if (b->pos < sizeof(b->buf)) {
            b->buf[b->pos] = '\0';
        }
    } else {
        b->pos += ret;
    }
}


void handle_message(const mavlink_message_t* msg) {
    struct buffer buf;
    buffer_init(&buf);

    // Emit timestamp, e.g. `[Mon Nov 11 13:51:06 2024]`
    time_t now = time(NULL);
    struct tm tm;
    // From `ctime(3)`: "According to POSIX.1-2001, localtime() is required to
    // behave as though tzset(3) was called, while localtime_r() does not have
    // this requirement.  For portable code, tzset(3) should be called before
    // localtime_r()."
    tzset();
    localtime_r(&now, &tm);

    buffer_printf(&buf, "[");
    buffer_strftime(&buf, "%c", &tm);
    buffer_printf(&buf, "] ");

    // Emit message name and `field=value` pairs.
    const mavlink_message_info_t* info = mavlink_get_message_info(msg);
    const char* payload = _MAV_PAYLOAD(msg);
    buffer_printf(&buf, "%s", info->name);
    for (unsigned i = 0; i < info->num_fields; ++i) {
        char delim = i == 0 ? ':' : ',';
        const mavlink_field_info_t* field = &info->fields[i];
        if (field->array_length > 0) {
            buffer_printf(&buf, "%c %s=<array>", delim, field->name);
        } else {
            switch (field->type) {
                case MAVLINK_TYPE_CHAR:
                    buffer_printf(&buf, "%c %s=%d", delim, field->name,
                            *(char*)(payload + field->wire_offset));
                    break;
                case MAVLINK_TYPE_UINT8_T:
                    buffer_printf(&buf, "%c %s=%" PRIu8, delim, field->name,
                            *(uint8_t*)(payload + field->wire_offset));
                    break;
                case MAVLINK_TYPE_INT8_T:
                    buffer_printf(&buf, "%c %s=%" PRId8, delim, field->name,
                            *(int8_t*)(payload + field->wire_offset));
                    break;
                case MAVLINK_TYPE_UINT16_T:
                    buffer_printf(&buf, "%c %s=%" PRIu16, delim, field->name,
                            *(uint16_t*)(payload + field->wire_offset));
                    break;
                case MAVLINK_TYPE_INT16_T:
                    buffer_printf(&buf, "%c %s=%" PRId16, delim, field->name,
                            *(int16_t*)(payload + field->wire_offset));
                    break;
                case MAVLINK_TYPE_UINT32_T:
                    buffer_printf(&buf, "%c %s=%" PRIu32, delim, field->name,
                            *(uint32_t*)(payload + field->wire_offset));
                    break;
                case MAVLINK_TYPE_INT32_T:
                    buffer_printf(&buf, "%c %s=%" PRId32, delim, field->name,
                            *(int32_t*)(payload + field->wire_offset));
                    break;
                case MAVLINK_TYPE_UINT64_T:
                    buffer_printf(&buf, "%c %s=%" PRIu64, delim, field->name,
                            *(uint64_t*)(payload + field->wire_offset));
                    break;
                case MAVLINK_TYPE_INT64_T:
                    buffer_printf(&buf, "%c %s=%" PRId64, delim, field->name,
                            *(int64_t*)(payload + field->wire_offset));
                    break;
                case MAVLINK_TYPE_FLOAT:
                    buffer_printf(&buf, "%c %s=%f", delim, field->name,
                            *(float*)(payload + field->wire_offset));
                    break;
                case MAVLINK_TYPE_DOUBLE:
                    buffer_printf(&buf, "%c %s=%lf", delim, field->name,
                            *(double*)(payload + field->wire_offset));
                    break;
            }
        }
    }
    buffer_printf(&buf, "\n");

    // Print the assembled line to stdout.
    printf("%s", buf.buf);
}


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
