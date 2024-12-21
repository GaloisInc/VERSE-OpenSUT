#include "io_trace.h"
#include <string.h>

ssize_t io_read(struct io_data* data, int fd, void* buf, size_t n) {
    // Return the next `n` bytes from `data->read_data`.  If `n` exceeds the
    // amount of data remaining, return as much data as possible.
    //
    // To be more thorough, we could instead truncate some reads (though not to
    // zero, which means EOF) in order to test the caller's handling of short
    // reads.  We could also return an error code (and set `errno`) in some
    // cases.
    //
    // We could also assert that `fd` is valid to check whether the caller is
    // passing bogus file descriptors.
    (void)fd;
    size_t remaining = data->read_data_len - data->read_pos;
    if (remaining == 0) {
        return 0;
    }
    if (n > remaining) {
        n = remaining;
    }
    memcpy(buf, data->read_data + data->read_pos, n);
    data->read_pos += n;
    return n;
}

ssize_t io_write(struct io_data* data, int fd, const void* buf, size_t n) {
    // Ignore inputs and return success (writing all `n` bytes).
    //
    // To be more thorough, we could instead truncate some writes (though not
    // to zero, which means EOF) in order to test the caller's handling of
    // short writes.  We could also return an error code (and set `errno`) in
    // some cases.
    (void)data;
    (void)fd;
    (void)buf;
    return n;
}

int io_shutdown(struct io_data* data, int fd, int how) {
    // Ignore inputs and return success.
    //
    // To be more thorough, we could return an error code (and set `errno`) in
    // some cases.
    (void)data;
    (void)fd;
    (void)how;
    return 0;
}
