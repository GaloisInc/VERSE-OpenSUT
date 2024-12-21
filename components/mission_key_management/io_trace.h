#pragma once

#include <stdint.h>
#include <stddef.h>
#include <sys/types.h>

#define READ_DATA_MAX_SIZE 64

struct io_data {
    const uint8_t* read_data;
    size_t read_data_len;
    size_t read_pos;
};

ssize_t io_read(struct io_data* data, int fd, void* buf, size_t n);
ssize_t io_write(struct io_data* data, int fd, const void* buf, size_t n);
int io_shutdown(struct io_data* data, int fd, int how);
