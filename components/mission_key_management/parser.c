#include "parser.h"
#include <stdio.h>
#include <string.h>
#include <unistd.h>

int parse_policy_entry(int fd, struct policy_entry* entry) {
    uint8_t buf[MEASURE_SIZE + KEY_ID_SIZE + KEY_SIZE];
    size_t pos = 0;
    while (pos < sizeof(buf)) {
        size_t need = sizeof(buf) - pos;
        ssize_t ret = read(fd, buf + pos, need);
        if (ret == -1) {
            perror("parse_policy_entry: read");
            return -1;
        } else if (ret == 0) {
            if (pos == 0) {
                return 0;
            } else {
                // We got some data before EOF, but not a complete record.
                fprintf(stderr, "parse_policy_entry: unexpected EOF\n");
                return -1;
            }
        }
        pos += ret;
    }

    const uint8_t* p = buf;
    memcpy(entry->measure, p, MEASURE_SIZE);
    p += MEASURE_SIZE;
    memcpy(entry->key_id, p, KEY_ID_SIZE);
    p += KEY_ID_SIZE;
    memcpy(entry->key, p, KEY_SIZE);
    p += KEY_SIZE;
    return 1;
}
