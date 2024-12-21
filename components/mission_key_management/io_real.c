#include "io_real.h"
#include <unistd.h>
#include <sys/socket.h>

ssize_t io_read(struct io_data* data, int fd, void* buf, size_t n) {
    (void)data;
    return read(fd, buf, n);
}
ssize_t io_write(struct io_data* data, int fd, const void* buf, size_t n) {
    (void)data;
    return write(fd, buf, n);
}
int io_shutdown(struct io_data* data, int fd, int how) {
    (void)data;
    return shutdown(fd, how);
}
