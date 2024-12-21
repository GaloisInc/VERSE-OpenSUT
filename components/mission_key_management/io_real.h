#pragma once

#include <stdint.h>
#include <stddef.h>
#include <sys/types.h>

struct io_data {
    uint8_t _dummy;
};

ssize_t io_read(struct io_data* data, int fd, void* buf, size_t n);
ssize_t io_write(struct io_data* data, int fd, const void* buf, size_t n);
int io_shutdown(struct io_data* data, int fd, int how);
