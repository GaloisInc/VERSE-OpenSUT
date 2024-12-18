#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <errno.h>
#include <limits.h>
#include <unistd.h>
#include <sys/socket.h>
#include <arpa/inet.h>
#include <netinet/in.h>

#define KEY_ID_SIZE 1
#define NONCE_SIZE 16
#define MEASURE_SIZE 32
#define HMAC_SIZE 32
#define ATTESTATION_SIZE (MEASURE_SIZE + HMAC_SIZE)
#define KEY_SIZE 32

//#define MKM_CLIENT_DEBUG

// Try to parse a string as an integer.  If parsing succeeds and the result is
// positive and no greater than `limit`, the result is stored in `*out` and the
// function returns `true`.  Otherwise, an error is printed to stderr, and the
// function returns `false`.  This function may modify `*out` arbitrarily on
// failure.
bool parse_long(const char* str, long* out, const char* desc, long limit) {
    if (str == NULL) {
        fprintf(stderr, "error parsing %s: NULL input\n", desc);
        return false;
    }
    if (*str == '\0') {
        fprintf(stderr, "error parsing %s: empty input\n", desc);
        return false;
    }

    char* end = NULL;
    errno = 0;
    *out = strtol(str, &end, 10);
    if (errno != 0) {
        fprintf(stderr, "error parsing %s: ", desc);
        perror("strtol");
        return false;
    }
    if (*end != '\0') {
        fprintf(stderr, "error parsing %s: contains non-digit characters\n", desc);
        return false;
    }
    if (*out < 0) {
        fprintf(stderr, "error parsing %s: value must be nonnegative\n", desc);
        return false;
    }
    if (*out > limit) {
        fprintf(stderr, "error parsing %s: value %ld is too large (limit = %ld)\n",
            desc, *out, limit);
        return false;
    }
    return true;
}


// Read exactly `count` bytes from `fd` into `buf`.  This will make multiple
// calls to `read` if needed.  Returns `true` on success; prints an error to
// stderr (mentioning `desc`) and returns `false` on error.
bool read_exact(int fd, void* buf, size_t count, const char* desc) {
#ifdef MKM_CLIENT_DEBUG
    fprintf(stderr, "read_exact: %s\n", desc);
#endif
    size_t pos = 0;
    while (pos < count) {
        ssize_t result = read(fd, (char*)buf + pos, count - pos);
#ifdef MKM_CLIENT_DEBUG
        fprintf(stderr, "read_exact: %s: %d\n", desc, (int)result);
#endif
        if (result < 0) {
            fprintf(stderr, "error %s: ", desc);
            perror("read");
            return false;
        } else if (result == 0) {
            fprintf(stderr, "error %s: unexpected EOF\n", desc);
            return false;
        } else {
            pos += result;
        }
    }
    return true;
}

bool write_exact(int fd, void* buf, size_t count, const char* desc) {
#ifdef MKM_CLIENT_DEBUG
    fprintf(stderr, "write_exact: %s\n", desc);
#endif
    size_t pos = 0;
    while (pos < count) {
        ssize_t result = write(fd, (const char*)buf + pos, count - pos);
#ifdef MKM_CLIENT_DEBUG
        fprintf(stderr, "write_exact: %s: %d\n", desc, (int)result);
#endif
        if (result < 0) {
            fprintf(stderr, "error %s: ", desc);
            perror("write");
            return false;
        } else if (result == 0) {
            fprintf(stderr, "error %s: unexpected EOF\n", desc);
            return false;
        } else {
            pos += result;
        }
    }
    return true;
}


int main(int argc, char *argv[]) {
    int ret;


    // Get the key ID from the command line arguments
    if (argc < 2) {
        fprintf(stderr, "usage: %s KEY_ID\n", argc > 0 ? argv[0] : "./mkm_client");
        return 1;
    }

    const char* key_id_str = argv[1];
    long key_id_long;
    ret = parse_long(key_id_str, &key_id_long, "key ID", (long)UINT8_MAX);
    if (!ret) {
        // `parse_long` already printed a message.
        return 1;
    }
    uint8_t key_id = (uint8_t)key_id_long;


    // Connect to the trusted boot daemon.
    const char* boot_sock_str = getenv("VERSE_TRUSTED_BOOT_FD");
    if (boot_sock_str == NULL) {
        fprintf(stderr, "error connecting to trusted boot daemon: "
            "$VERSE_TRUSTED_BOOT_FD is unset\n");
        return 1;
    }

    long boot_sock_long;
    ret = parse_long(boot_sock_str, &boot_sock_long, "$VERSE_TRUSTED_BOOT_FD", (long)INT_MAX);
    if (!ret) {
        return 1;
    }
    int boot_sock = (int)boot_sock_long;


    // Connect to the MKM server.
    int mkm_sock = socket(AF_INET, SOCK_STREAM, 0);
    if (mkm_sock < 0) {
        perror("error creating MKM socket: socket");
        return 1;
    }

    struct sockaddr_in host_addr = {0};
    host_addr.sin_family = AF_INET;

    const char* host_addr_str = getenv("MKM_HOST");
    if (host_addr_str == NULL) {
        host_addr_str = "127.0.0.1";
    }
    ret = inet_pton(host_addr.sin_family, host_addr_str, &host_addr.sin_addr);
    if (ret == 0) {
        fprintf(stderr, "bad address in $MKM_HOST: %s\n", host_addr_str);
        return 1;
    } else if (ret < 0) {
        perror("error parsing MKM host address: inet_pton");
        return 1;
    }

    uint16_t port = 6000;
    const char* port_str = getenv("MKM_PORT");
    if (port_str != NULL) {
        long port_long;
        ret = parse_long(port_str, &port_long, "port number", (long)UINT16_MAX);
        if (!ret) {
            return 1;
        }
        port = (int)port_long;
    }
    host_addr.sin_port = htons(port);

    ret = connect(mkm_sock, (const struct sockaddr*)&host_addr, sizeof(host_addr));
    if (ret != 0) {
        perror("error connecting to MKM server: connect");
        return 1;
    }
    fprintf(stderr, "connected to MKM server at %s:%d\n",
        host_addr_str, ntohs(host_addr.sin_port));


    // Run the protocol.
    ret = write_exact(mkm_sock, &key_id, 1,
        "sending key ID to MKM");
    if (!ret) {
        return 1;
    }

    uint8_t nonce[NONCE_SIZE];
    ret = read_exact(mkm_sock, nonce, sizeof(nonce),
        "receiving nonce from MKM");
    if (!ret) {
        return 1;
    }

    // Command 2 is the attest operation
    uint8_t trusted_boot_cmd = 2;
    ret = write_exact(boot_sock, &trusted_boot_cmd, 1,
        "sending command to trusted boot daemon");
    if (!ret) {
        return 1;
    }

    ret = write_exact(boot_sock, nonce, sizeof(nonce),
        "sending nonce to trusted boot daemon");
    if (!ret) {
        return 1;
    }

    uint8_t attestation[ATTESTATION_SIZE];
    ret = read_exact(boot_sock, attestation, sizeof(attestation),
        "receiving attestation from trusted boot daemon");
    if (!ret) {
        return 1;
    }

    ret = write_exact(mkm_sock, attestation, sizeof(attestation),
        "sending attestation to MKM");
    if (!ret) {
        return 1;
    }

    uint8_t key[KEY_SIZE];
    ret = read_exact(mkm_sock, key, sizeof(key),
        "receiving key from MKM");
    if (!ret) {
        return 1;
    }

    ret = write_exact(1, key, sizeof(key),
        "writing key to stdout");
    if (!ret) {
        return 1;
    }

    return 0;
}
