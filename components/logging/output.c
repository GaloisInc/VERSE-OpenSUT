// Code for converting a MAVLink message into log output.

#include <stdarg.h>
#include <stdlib.h>
#include <inttypes.h>
#include <sys/types.h>

#ifndef CN_ENV
# include <stdio.h>
# include <time.h>
// `mavlink_get_info.h` uses `offsetof`, but doesn't include the header
// `stddef.h` that provides it.  We include the header here so `offsetof` will
// be available.
# include <stddef.h>
# include <mavlink/all/mavlink.h>
# include <mavlink/mavlink_get_info.h>
#else
# include "cn_stubs.h"
# include "cn_mavlink_stubs.h"
#endif

#include "output.h"


// Buffer type for building up a single line of log output.
struct buffer {
    size_t pos;
    char buf[4096];
};

void buffer_init(struct buffer* b) {
    b->pos = 0;
    b->buf[0] = '\0';
}


#ifndef CN_ENV

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

#else

// Dispatch by argument count to different variants of `buffer_printf`.
//
// Conveniently, we never call `buffer_printf` twice with the same number of
// arguments but with different argument types.  If this changes, we could
// potentially handle it by making all variants take `void*` and wrap each
// variant in a macro that inserts the necessary casts.

#define buffer_printf(...) VA_SELECT(buffer_printf, __VA_ARGS__)

void buffer_printf_2(struct buffer* b, const char* fmt) {
    // TODO
}

void buffer_printf_3(struct buffer* b, const char* fmt, const char* arg0) {
    // TODO
}

void buffer_printf_4(struct buffer* b, const char* fmt, int arg0, const char* arg1) {
    // TODO
}

void buffer_printf_5(struct buffer* b, const char* fmt,
        int arg0, const char* arg1, int64_t arg2) {
    // TODO
}

#endif


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


// Process a message and write the data it contains to the log.
//
// Requirement 1: The logging component shall ... record some or all telemetry
// values to disk.
//
// Requirement 2: Logs shall be saved in text format, with a timestamp on each
// line.
//
// Requirement 2.1: Logs may be printed to stdout for debugging purposes.
//
// This code always prints to stdout.  The setup code will redirect stdout to
// the encrypted filesystem before calling this.
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
// CN doesn't support floats.
#ifndef CN_ENV
                    buffer_printf(&buf, "%c %s=%f", delim, field->name,
                            *(float*)(payload + field->wire_offset));
#endif
                    break;
                case MAVLINK_TYPE_DOUBLE:
#ifndef CN_ENV
                    buffer_printf(&buf, "%c %s=%lf", delim, field->name,
                            *(double*)(payload + field->wire_offset));
#endif
                    break;
            }
        }
    }
    buffer_printf(&buf, "\n");

    // Print the assembled line to stdout.
    printf("%s", buf.buf);
}
