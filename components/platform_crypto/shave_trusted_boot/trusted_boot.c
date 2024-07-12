#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <fcntl.h>
#include <signal.h>
#include <sys/stat.h>
#include <sys/socket.h>
#include <sys/mman.h>
#include <sys/wait.h>

#include "sha_256.h"
#include "hmac_sha256.h"

extern char** environ;


#ifdef VERBOSE
void print_hex(const char* desc, const void* data, size_t size) {
    fprintf(stderr, "%s: ", desc);
    for (size_t i = 0; i < size; ++i) {
        fprintf(stderr, "%02x", ((const uint8_t*)data)[i]);
    }
    fprintf(stderr, "\n");
}
#endif


#define SHA256_SIZE  (256 / 8)
#define MEASURE_SIZE SHA256_SIZE

static uint8_t current_measure[MEASURE_SIZE] = {0};

/**
 * Update `current_measure` by hashing it together with the additional data
 * from the region `start_address .. end_address`.
 */
void measure(
    void* start_address,
    void* end_address
) {
    SHA256_CTX ctx;
    SHA256_Init(&ctx);

    size_t size = end_address - start_address;
    SHA256_Update(&ctx, start_address, size);

    SHA256_Update(&ctx, current_measure, sizeof(current_measure));

    SHA256_Final(current_measure, &ctx);

#ifdef VERBOSE
    print_hex("measure", current_measure, MEASURE_SIZE);
#endif
}

static int boot_once = 0;

/**
 * Hash that the memory region `start_address .. end_address` and compare the
 * resulting measurement to `expected_measure`.  If they match, call `entry()`.
 *
 * `end_address` is an exclusive bound.
 *
 * This is designed to mimic a bare-metal trusted boot API.  In that case,
 * `entry` would point somewhere within `start_address .. end_address`.
 * However, we don't enforce this, which makes this function usable in
 * non-bare-metal cases as well.
 */
int boot(
    void* start_address,
    void* end_address,
    const uint8_t* expected_measure,
    void (*entry)()
) {
    if (boot_once) {
        return -1;
    }

    measure(start_address, end_address);
    if (expected_measure != NULL
            && memcmp(current_measure, expected_measure, SHA256_SIZE) != 0) {
        return -1;
    }

    boot_once = 1;

    // TODO: For the embedded version of this code, at this point we should
    // zero memory (aside from `start_address .. end_address`, registers, and
    // any other visible state.  This may require assembly code.

    entry();

    // We normally expect `entry` not to return, so this won't usually be
    // reachable.
    return -1;
}


#define KEY_SIZE 32
#define NONCE_SIZE 16
#define HMAC_SIZE 32
static const uint8_t key[KEY_SIZE] = {0};

/**
 * Produce an attestation of the current measurement value.  This concatenates
 * the current measurement with `nonce`, computes the HMAC using the secret
 * `key`, and writes the result to `hmac`.  It also copies the current
 * measurement into `measure`.
 *
 * If `hmac` is null, then nothing is written to `hmac`, and similarly for
 * `measure`.
 */
void attest(
    const uint8_t* nonce,
    uint8_t* measure,
    uint8_t* hmac
) {
    if (measure != NULL) {
        memcpy(measure, current_measure, MEASURE_SIZE);
    }

    if (hmac != NULL) {
        uint8_t hmac_input[MEASURE_SIZE + NONCE_SIZE];
        memcpy(&hmac_input[0], current_measure, MEASURE_SIZE);
        memcpy(&hmac_input[MEASURE_SIZE], nonce, NONCE_SIZE);
        hmac_sha256(key, KEY_SIZE, hmac_input, sizeof(hmac_input), hmac);
    }
}


// Linux (non-bare-metal) entry point

// Read `count` bytes from `buf`, making multiple `read` calls if necessary.
// Returns `count` on success, a value in the range `0 <= x < count` if EOF was
// reached before `count` bytes count be read, or a negative value on error.
// If an error occurs, the amount of data read before the error is not
// reported.
int read_exact(int fd, void* buf, size_t count) {
    size_t total = 0;
    while (total < count) {
        fprintf(stderr, "read_exact: at %d/%d\n", total, count);
        int ret = read(fd, buf + total, count - total);
        fprintf(stderr, "  got %d\n", ret);
        if (ret < 0) {
            return ret;
        } else if (ret == 0) {
            break;
        }
        total += ret;
    }
    return total;
}

int write_exact(int fd, const void* buf, size_t count) {
    size_t total = 0;
    while (total < count) {
        int ret = write(fd, buf + total, count - total);
        if (ret < 0) {
            return ret;
        } else if (ret == 0) {
            break;
        }
        total += ret;
    }
    return total;
}

static char* binary_path = NULL;
static int binary_fd = -1;

void linux_run() {
    int socket_fds[2];
    int ret = socketpair(AF_UNIX, SOCK_STREAM, 0, socket_fds);
    if (ret != 0) {
        perror("failed to create socket pair");
        exit(2);
    }

    ret = fcntl(socket_fds[0], F_SETFD, FD_CLOEXEC);
    if (ret != 0) {
        perror("failed to set CLOEXEC for parent socket");
    }

    int child_pid = -1;
    if ((child_pid = fork()) == 0) {
        // Make a new process group for the child, so the child and its
        // descendants can all be killed at once.
        /*
        ret = setpgid(0, 0);
        if (ret != 0) {
            perror("failed to set process group");
            exit(3);
        }
        */

        char env_buf[64] = {0};
        ret = snprintf(env_buf, sizeof(env_buf), "VERSE_TRUSTED_BOOT_FD=%d", socket_fds[1]);
        if (ret < 0 || ret >= sizeof(env_buf)) {
            perror("failed to build environment string");
            exit(3);
        }
        putenv(env_buf);

        char *argv[] = { binary_path, NULL };
        int ret = execve(binary_path, argv, environ);
        if (ret < 0) {
            perror("failed to exec binary");
            exit(3);
        }
    }
    // The rest of this function runs as the parent.

    if (child_pid < 0) {
        perror("failed to fork");
        exit(2);
    }

    ret = close(socket_fds[1]);
    if (ret < 0) {
        perror("failed to close the child socket");
        goto error;
    }

    // Process requests until the child closes the socket.
    int socket_fd = socket_fds[0];
    for (;;) {
        uint8_t cmd;
        ret = read_exact(socket_fd, &cmd, sizeof(cmd));
        if (ret == 0) {
            // Socket has been closed.
            break;
        } else if (ret != sizeof(cmd)) {
            goto socket_read_error;
        }

        switch (cmd) {
            case 1:
                // Measure
                {
                    uint16_t data_size;
                    ret = read_exact(socket_fd, &data_size, sizeof(data_size));
                    if (ret != sizeof(data_size)) {
                        goto socket_read_error;
                    }

                    uint8_t* buf = malloc(data_size);
                    ret = read_exact(socket_fd, buf, data_size);
                    if (ret != data_size) {
                        free(buf);
                        goto socket_read_error;
                    }

                    measure(buf, buf + data_size);
                    free(buf);
                }
                break;
            case 2:
                // Attest
                {
                    uint8_t nonce[NONCE_SIZE];
                    ret = read_exact(socket_fd, nonce, sizeof(nonce));
                    if (ret != sizeof(nonce)) {
                        goto socket_read_error;
                    }

                    uint8_t output[MEASURE_SIZE + HMAC_SIZE];
                    attest(nonce, &output[0], &output[MEASURE_SIZE]);

                    ret = write_exact(socket_fd, output, sizeof(output));
                    if (ret != sizeof(output)) {
                        goto socket_write_error;
                    }
                }
                break;
            default:
                fprintf(stderr, "invalid command 0x%02x\n", cmd);
                goto error;
        }
    }

    // Wait for child to exit.
    for (;;) {
        int status = 0;
        pid_t exited_pid = waitpid(-1, &status, 0);
        if (exited_pid < 0) {
            perror("failed while waiting for child");
            goto error;
        }

        if (exited_pid == child_pid) {
            if (WIFEXITED(status)) {
                exit(WEXITSTATUS(status));
            } else if (WIFSIGNALED(status)) {
                exit(128 + WTERMSIG(status));
            }
        }
        // Otherwise, keep waiting for the child to terminate.
    }

    // Unreachable.


socket_read_error:
    if (ret < 0) {
        perror("failed to read from socket");
        goto error;
    } else {
        fprintf(stderr, "unexpected EOF while reading from socket (after %d bytes)\n", ret);
        goto error;
    }

socket_write_error:
    if (ret < 0) {
        perror("failed to write to socket");
        goto error;
    } else {
        fprintf(stderr, "unexpected EOF while writing to socket (after %d bytes)\n", ret);
        goto error;
    }

error:
    // There's no guarantee that the child succeeds in creating a new
    // process group, so we also try to kill the child directly.
    kill(child_pid, SIGTERM);
    //kill(-child_pid, SIGTERM);
    exit(2);
}

int parse_hex_char(char c) {
    if ('0' <= c && c <= '9') {
        return c - '0';
    } else if ('a' <= c && c <= 'f') {
        return c - 'a' + 10;
    } else if ('A' <= c && c <= 'F') {
        return c - 'A' + 10;
    } else {
        return -1;
    }
}

int parse_hex_str(const char* str, uint8_t* dest, size_t dest_size) {
    const char* cur = str;
    for (size_t i = 0; i < dest_size; ++i) {
        // `strtol` is quite lenient in the input formats it accepts (e.g.
        // `+0xff` is the same as `ff`), which we don't want.

        // If the string `str` is too short, we'll end up calling
        // `parse_hex_char('\0')` and bailing out immediately after.
        int x1 = parse_hex_char(*cur);
        if (x1 < 0) {
            return -1;
        }
        int x2 = parse_hex_char(*(cur + 1));
        if (x2 < 0) {
            return -1;
        }
        cur += 2;

        dest[i] = (x1 << 4) | x2;
    }

    return 0;
}

int main(int argc, char *argv[]) {
    if (argc != 2 && argc != 3) {
        fprintf(stderr, "usage: %s binary [expected_hash]\n",
            argc >= 1 ? argv[0] : "trusted_boot");
        return 1;
    }

    binary_path = argv[1];

    const char* expected_measure_str = NULL;
    uint8_t expected_measure[MEASURE_SIZE];
    int ret = -1;
    if (argc >= 3) {
        expected_measure_str = argv[2];
        ret = parse_hex_str(expected_measure_str, expected_measure, sizeof(expected_measure));
        if (ret != 0) {
            fprintf(stderr, "failed to parse expected measure\n");
            return 1;
        }
    }

    // Open the binary so we can mmap and hash it.
    binary_fd = open(binary_path, O_RDONLY | O_CLOEXEC);
    if (binary_fd < 0) {
        perror("failed to open binary");
        return 1;
    }

    struct stat st;
    ret = fstat(binary_fd, &st);
    if (ret != 0) {
        perror("failed to stat binary");
        return 1;
    }

    void* start = mmap(NULL, st.st_size, PROT_READ, MAP_SHARED, binary_fd, 0);
    if (start == MAP_FAILED) {
        perror("failed to mmap binary");
        return 1;
    }

    boot(start, start + st.st_size,
        expected_measure_str != NULL ? expected_measure : NULL,
        linux_run);
}
