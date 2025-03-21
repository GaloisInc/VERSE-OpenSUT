#include <stdlib.h>
#include <stdint.h>
#include <limits.h>

/*$ function (i32) INT_MAX() $*/
static
int32_t c_INT_MAX() /*$ cn_function INT_MAX; $*/ { return INT_MAX; }

#include <stdio.h>
#include <string.h>
#ifndef CN_ENV
#include <unistd.h>
#include <fcntl.h>
#endif
#include <signal.h>
#ifndef CN_ENV
#include <sys/stat.h>
#include <sys/socket.h>
#include <sys/mman.h>
#include <sys/wait.h>
#endif
#ifdef CN_ENV
#include "cn_memory.h"
#include "cn_strings.h"
#include "cn_array_utils.h"

/*$ spec snprintf(pointer p, size_t n, pointer f);
  requires true;
  ensures true;
$*/

/*$ spec fprintf(pointer p, pointer f);
  requires true;
  ensures true;
$*/

typedef int pid_t;
ssize_t read(int fildes, void *buf, size_t n);
ssize_t _read(int fildes, void *buf, size_t n);
/*$ spec _read(i32 fildes, pointer buf, u64 n);
  // @PropertyClass: P1-LAC
  // @PropertyClass: P3-SOP
  // @PropertyClass: P6-UserDefPred
    requires
      take bufi = ArrayBlock_u8(buf, n);
    ensures
     return >= -1i64 && return <= (i64)n;
     // return == -1 -> no owned, all block
     // return >= 0 < n -> 0 <= owned < return, return <= block < n
     // return == n -> 0 <= owned < n, return <= block < n
     take bufo = each(u64 i; (return == -1i64) ? false : (0u64 <= i && i <(u64)return)) {Owned<uint8_t>(array_shift<uint8_t>(buf, i))};
     take bufb = each(u64 i; (return == -1i64) ? (0u64 <= i && i < n) : ((u64)return <= i && i < n)) {Block<uint8_t>(array_shift<uint8_t>(buf, i))};
$*/
#define read(f,b,s) _read(f,b,s)
ssize_t write(int fildes, const void *buf, size_t nbyte);
ssize_t _write(int fildes, const void *buf, size_t nbyte);
/*$ spec _write(i32 fildes, pointer buf, u64 nbyte);
  // @PropertyClass: P1-LAC
  // @PropertyClass: P3-SOP
  requires
    ((i32)nbyte) >= 0i32;
    take bufi = each(u64 i; i >= 0u64 && i < nbyte) {Owned<uint8_t>(array_shift<uint8_t>(buf,i))};
  ensures
    take bufo = each(u64 i; i >= 0u64 && i < nbyte) {Owned<uint8_t>(array_shift<uint8_t>(buf,i))};
    bufi == bufo;
    return >= -1i64 && return < (i64)nbyte;
$*/
#define write(f,b,s) _write(f,b,s)
#define memcpy(f,b,s) _memcpy(f,b,s)
#define memcmp(f,b,s) _memcmp(f,b,s)

#define malloc(x) _malloc(x)
#define free(x) _free(x)

int
socketpair(int domain, int type, int protocol, int socket_vector[2]);
/*$ spec socketpair(i32 domain, i32 type, i32 protocol, pointer socket_vector);
  // @PropertyClass: P3-SOP
    requires take svi = Block<int[2]>(socket_vector);
    ensures take svo = Owned<int[2]>(socket_vector);
      svo[0u64] != svo[1u64];
    // TODO
$*/
#define AF_UNIX 1
#define SOCK_STREAM 1
#define fcntl(...) 0

pid_t fork(void);
/*$ spec fork();
    requires true;
    ensures true;
$*/
int putenv(char *string);
/*$ spec putenv(pointer string);
    requires true;
    ensures true;
$*/
int execve(const char *path, char *const argv[], char *const envp[]);
/*$ spec execve(pointer path, pointer argv, pointer envp);
    requires true;
    ensures true;
$*/
int close(int fildes);
int _close(int fildes);
/*$ spec _close(i32 fildes);
    requires true;
    ensures true;
$*/
#define close(x) _close(x)
pid_t waitpid(pid_t pid, int *stat_loc, int options);
/*$ spec waitpid(i32 pid, pointer stat_loc, i32 options);
    requires true;
    ensures true;
$*/
#define WIFEXITED(x) (x & 1)
#define WEXITSTATUS(x) (x & 2)
#define WIFSIGNALED(x) (x & 3)
#define WTERMSIG(x) (x & 4)
int
kill(pid_t pid, int sig);
/*$ spec kill(i32 pid, i32 sig);
    requires true;
    ensures true;
$*/
//int open(const char *path, int oflag, ...);
int open(const char *path, int oflag);
int _open(const char *path, int oflag);
/*$ spec _open(pointer path, i32 oflag);
  // @PropertyClass: P3-SOP
    requires take pi = Owned<char>(path);
    ensures take po = Owned<char>(path);
      pi == po;
$*/
#define open(a,b) _open(a,b);
#define O_RDONLY 1
#define O_CLOEXEC 2
struct stat {
    int st_size;
};
int
fstat(int fildes, struct stat *buf);
/*$ spec fstat(i32 fildes, pointer buf);
  // @PropertyClass: P3-SOP
  requires
    take bi = Block<struct stat>(buf);
  ensures
    take bo = Owned<struct stat>(buf);
$*/
// TODO need support for multiple allocation types to ensure free can't be
// called on mmap'd regions
void *
mmap(void *addr, size_t len, int prot, int flags, int fd, off_t offset);
/*$ spec mmap(pointer addr, u64 len, i32 prot, i32 flags, i32 fd, i64 offset);
  // @PropertyClass: P3-SOP
  requires
    true;
  ensures
    take log = Alloc(return);
    allocs[(alloc_id)return] == log;
    log.base == (u64) return;
    log.size == len;
    take o = each(u64 j; j >= 0u64 && j < len) {Block<uint8_t>(array_shift<uint8_t>(return, j))};
$*/
int munmap(void *addr, size_t len);
/*$ spec munmap(pointer addr, u64 len);
  // @PropertyClass: P3-SOP
  requires
    !is_null(addr);
    take log = Alloc(addr);
    allocs[(alloc_id)addr] == log;
    let base = array_shift<char>(addr, 0u64);
    log.base == (u64) base;
    log.size == len;
    take i = each(u64 j; j >= 0u64 && j < len) {Block<uint8_t>(array_shift<uint8_t>(addr, j))};
  ensures
    true;
$*/
#define MAP_SHARED 1
#define MAP_FAILED NULL
#define PROT_READ 2
#ifndef WAR_CN_309
// not possible to call this due to CN issue #309
// this spec isn't right but can't develop it at all without #309
void perror(const char *msg);
/*$ spec perror(pointer msg);
  // @PropertyClass: P3-SOP
    requires take mi = Owned<char>(msg);
    ensures take mo = Owned<char>(msg);
      mi == mo;
$*/
#else
#define perror(...) 0
#endif
/*$ spec exit(i32 v);
    requires true;
    ensures true;
$*/
#endif

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
/*$ function (u64) MEASURE_SIZE() $*/
static
uint64_t c_MEASURE_SIZE() /*$ cn_function MEASURE_SIZE; $*/ { return MEASURE_SIZE; }

static uint8_t current_measure[MEASURE_SIZE] = {0};

/**
 * Update `current_measure` by hashing it together with the additional data
 * from the region `start_address .. end_address`.
 */
void measure(
    void* start_address,
    void* end_address
)
/*$
  // @PropertyClass: P1-LAC
  // @PropertyClass: P3-SOP
  accesses current_measure;
  requires
    take si = each(u64 i; i >= 0u64 && i < (((u64)end_address) - ((u64)start_address))) { Owned<uint8_t>(array_shift<uint8_t>(start_address, i))};

  ensures
    take so = each(u64 i; i >= 0u64 && i < (((u64)end_address) - ((u64)start_address))) { Owned<uint8_t>(array_shift<uint8_t>(start_address, i))};
$*/
{
    SHA256_CTX ctx;
    SHA256_Init(&ctx);

    uintptr_t e = (uintptr_t)end_address;
    uintptr_t s = (uintptr_t)start_address;
#ifndef CN_ENV
    size_t size = end_address - start_address;
#else
    size_t size =  e > s ? e - s : 0;
#endif
    SHA256_Update(&ctx, start_address, size);

    SHA256_Update(&ctx, current_measure, sizeof(current_measure));

    SHA256_Final(current_measure, &ctx);

#ifdef VERBOSE
    print_hex("measure", current_measure, MEASURE_SIZE);
#endif
}

static int boot_once = 0;

// TODO there is currently no way to require a function pointer to be valid in
// CN. Additionally the argument here is going to be a pointer to the entry
// vector of an executable, and thus outside of the C VM anyway.
static void magically_call(void (*f)(void))
/*$ trusted; $*/
{
  f();
}

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
    void (*entry)(void)
)
/*$
  // @PropertyClass: P1-LAC
  // @PropertyClass: P3-SOP
  // @PropertyClass: P6-UserDefPred
  accesses boot_once;
  accesses current_measure;
  requires
    take si = each(u64 i; i >= 0u64 && i < (((u64)end_address) - ((u64)start_address))) { Owned<uint8_t>(array_shift<uint8_t>(start_address, i))};
    take emi = ArrayOrNull_u8(expected_measure, MEASURE_SIZE());

  ensures
    take so = each(u64 i; i >= 0u64 && i < (((u64)end_address) - ((u64)start_address))) { Owned<uint8_t>(array_shift<uint8_t>(start_address, i))};
    take emo = ArrayOrNull_u8(expected_measure, MEASURE_SIZE());
    emi == emo;
$*/
{
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

#ifndef CN_ENV
    entry();
#else
    void (*f)(void) = (void (*)(void))entry;
    magically_call(f);
#endif

    // We normally expect `entry` not to return, so this won't usually be
    // reachable.
    return -1;
}


#define KEY_SIZE 32
/*$ function (u64) KEY_SIZE() $*/
static
uint64_t c_KEY_SIZE() /*$ cn_function KEY_SIZE; $*/ { return KEY_SIZE; }
#define NONCE_SIZE 16
/*$ function (u64) NONCE_SIZE() $*/
static
uint64_t c_NONCE_SIZE() /*$ cn_function NONCE_SIZE; $*/ { return NONCE_SIZE; }
#define HMAC_SIZE 32
/*$ function (u64) HMAC_SIZE() $*/
static
uint64_t c_HMAC_SIZE() /*$ cn_function HMAC_SIZE; $*/ { return HMAC_SIZE; }

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
)
/*$
  // @PropertyClass: P3-SOP
  // @PropertyClass: P6-UserDefPred
  accesses current_measure;
  accesses key;
  requires
    take ni = each(u64 i; i >= 0u64 && i < NONCE_SIZE()) {Owned<uint8_t>(array_shift(nonce,i))};
    take mi = ArrayOrNull_Block_u8(measure, MEASURE_SIZE());
    take hi = ArrayOrNull_Block_u8(hmac, HMAC_SIZE());
  ensures
    take no = each(u64 i; i >= 0u64 && i < NONCE_SIZE()) {Owned<uint8_t>(array_shift(nonce,i))};
    take mo = ArrayOrNull_u8(measure, MEASURE_SIZE());
    take ho = ArrayOrNull_u8(hmac, HMAC_SIZE());
    ni == no;
$*/
{
    if (measure != NULL) {
        memcpy(measure, current_measure, MEASURE_SIZE);
    }

    if (hmac != NULL) {
        uint8_t hmac_input[MEASURE_SIZE + NONCE_SIZE];
        uint8_t *hmac_input_0 = hmac_input;
        uint8_t *hmac_input_MEASURE_SIZE = &hmac_input[MEASURE_SIZE];

        /*$ apply SplitAt_Block_u8(hmac_input_0, MEASURE_SIZE()+NONCE_SIZE(), MEASURE_SIZE(), NONCE_SIZE()); $*/
        memcpy(&hmac_input[0], current_measure, MEASURE_SIZE);
        /*$ apply ViewShift_Block_u8(hmac_input_0, hmac_input_MEASURE_SIZE, MEASURE_SIZE(), NONCE_SIZE()); $*/
        memcpy(&hmac_input[MEASURE_SIZE], nonce, NONCE_SIZE);
        /*$ apply UnViewShift_Owned_u8(hmac_input_0, hmac_input_MEASURE_SIZE, MEASURE_SIZE(), NONCE_SIZE()); $*/
        /*$ apply UnSplitAt_Owned_u8(hmac_input_0, MEASURE_SIZE()+NONCE_SIZE(), MEASURE_SIZE(), NONCE_SIZE()); $*/
        hmac_sha256(key, KEY_SIZE, hmac_input, sizeof(hmac_input), hmac);
    }
}


// Linux (non-bare-metal) entry point

// Read `count` bytes from `buf`, making multiple `read` calls if necessary.
// Returns `count` on success, a value in the range `0 <= x < count` if EOF was
// reached before `count` bytes count be read, or a negative value on error.
// If an error occurs, the amount of data read before the error is not
// reported.
int read_exact(int fd, void* buf, size_t count)
/*$
  // @PropertyClass: P1-LAC
  // @PropertyClass: P3-SOP
  // @PropertyClass: P6-UserDefPred
    accesses __stderr;
    requires
      count < (u64)INT_MAX();
      take bufi = ArrayBlock_u8(buf, count);
    ensures
     return >= -1i32 && return <= (i32)count;
     // return == -1 -> no owned, all block
     // return >= 0 < count -> 0 <= owned < return, return <= block < count
     // return == count -> 0 <= owned < count, return <= block < count
     take bufo = each(u64 i; (return == -1i32) ? false : (0u64 <= i && i <(u64)return)) {Owned<uint8_t>(array_shift<uint8_t>(buf, i))};
     take bufb = each(u64 i; (return == -1i32) ? (0u64 <= i && i < count) : ((u64)return <= i && i < count)) {Block<uint8_t>(array_shift<uint8_t>(buf, i))};
$*/
{
    size_t total = 0;
    while (total < count)
    /*$ inv
        total >= 0u64;
        total <= count;
        ((u64)(u32)total) == total;
        {buf} unchanged;
        {count} unchanged;
        take bufbinv = each(u64 i; total <= i && i < count) {Block<uint8_t>(array_shift<uint8_t>(buf, i))};
        take bufoinv = each(u64 i; 0u64 <= i && i < total) {Owned<uint8_t>(array_shift<uint8_t>(buf, i))};
    $*/
    {
        /*$ assert(total < count); $*/
        uint8_t *buf_0 = (uint8_t*)buf;
        /*$ extract Block<uint8_t>, (u64)total; $*/
        uint8_t *buf_total = &((uint8_t*)buf)[total];
        fprintf(stderr, "read_exact: at %ld/%ld\n", total, count);

        /*$ apply ViewShift_Block_u8(buf_0, buf_total, total, count - total); $*/
        ssize_t ret = read(fd, ((uint8_t*)buf) + total, count - total);
        fprintf(stderr, "  got %ld\n", ret);
        if (ret < 0) {
            /*$ apply UnViewShift_Block_u8(buf_0, buf_total, total, count - total); $*/
            /*$ apply UnSplitAt_Block_u8(buf_0, count, total, 1u64);$*/
            return ret;
        } else if (ret == 0) {
            /*$ apply UnViewShift_Block_u8(buf_0, buf_total, total, count - total); $*/
            break;
        }
        /*$ apply UnViewShift_Owned_u8(buf_0, buf_total, total, (u64)ret); $*/
        /*$ apply UnViewShift_Block_At_u8(buf_0, buf_total, total, (u64)ret, count - total); $*/
        /*$ apply UnSplitAt_Owned_u8(buf_0, total+(u64)ret, total, (u64)ret); $*/
        total += ret;
    }
    /*$ assert(total <= count); $*/
    return total;
}

int write_exact(int fd, const void* buf, size_t count)
/*$
  // @PropertyClass: P1-LAC
  // @PropertyClass: P3-SOP
  // @PropertyClass: P6-UserDefPred
  requires
    count < (u64)INT_MAX();
    take bufi = each(u64 i; i >= 0u64 && i < count) {Owned<uint8_t>(array_shift<uint8_t>(buf,i))};
  ensures
    take bufo = each(u64 i; i >= 0u64 && i < count) {Owned<uint8_t>(array_shift<uint8_t>(buf,i))};
    // TODO because we are splitting and merging these so much this is going to be very tricky to determine
    //bufi == bufo;
    return >= -1i32 && return <= (i32)count;
$*/
{
    size_t total = 0;
    while (total < count)
    /*$ inv
        total <= count;
        {count} unchanged;
        {buf} unchanged;
        take bufinv = each(u64 i; i >= 0u64 && i < count) {Owned<uint8_t>(array_shift<uint8_t>(buf,i))};
    $*/
    {
        uint8_t *buf_0 = (uint8_t*)buf;
        /*$ extract Owned<uint8_t>, (u64)total; $*/
        uint8_t *buf_total = &((uint8_t*)buf)[total];

        /*$ apply SplitAt_Owned_u8(buf_0, count, total, count - total); $*/
        /*$ apply ViewShift_Owned_u8(buf_0, buf_total, total, count - total); $*/
        int ret = write(fd, ((uint8_t*)buf) + total, count - total);
        /*$ apply UnViewShift_Owned_u8(buf_0, buf_total, total, count - total); $*/
        /*$ apply UnSplitAt_Owned_u8(buf_0, count, total, count - total); $*/

        if (ret < 0) {
            return ret;
        } else if (ret == 0) {
            break;
        }
        total += (uint64_t)ret;
    }
    return total;
}

static char* binary_path = NULL;
static int binary_fd = -1;

void linux_run()
/*$
  // @PropertyClass: P3-SOP
  // @PropertyClass: P6-UserDefPred
  accesses binary_path;
  accesses environ;
  accesses current_measure;
  accesses key;
  accesses __stderr;
$*/
{
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

    /*$ extract Owned<int>, 1u64; $*/
    ret = close(socket_fds[1]);
    if (ret < 0) {
        perror("failed to close the child socket");
        goto error;
    }

    // Process requests until the child closes the socket.
    /*$ extract Owned<int>, 0u64; $*/
    int socket_fd = socket_fds[0];
    for (;;) {
        uint8_t cmd;
        /*$ extract Block<uint8_t>, 0u64; $*/
        ret = read_exact(socket_fd, &cmd, sizeof(cmd));
        if (ret == 0) {
            // Socket has been closed.
            break;
        } else if (ret != sizeof(cmd)) {
            goto socket_read_error;
        }

        /*$ extract Owned<uint8_t>, 0u64; $*/
        switch (cmd) {
            case 1:
                // Measure
                {
                    uint16_t data_size;
                    uint16_t *data_size_ = &data_size; // necessary because of a restriction on lemmas in CN
                    /*$ extract Block<uint16_t>, 0u64; $*/
                    /*$ apply TransmuteArray_Block_u16_u8(data_size_, 1u64); $*/
                    ret = read_exact(socket_fd, &data_size, sizeof(data_size));
                    if (ret != sizeof(data_size)) {
                        /*$ apply ForgetPartialInit_u8(data_size_, 2u64, ret == -1i32 ? 0u64 : (u64)ret); $*/
                        /*$ apply UnTransmuteArray_Block_u16_u8(data_size_, 1u64); $*/
                        goto socket_read_error;
                    }

                    /*$ apply UnTransmuteArray_Owned_u16_u8(data_size_, 1u64); $*/
                    /*$ extract Owned<uint16_t>, 0u64; $*/
                    if (data_size == 0) {
                        goto error;
                    }
                    uint8_t* buf = malloc(data_size);
                    ret = read_exact(socket_fd, buf, data_size);
                    if (ret != data_size) {
                        /*$ apply ForgetPartialInit_u8(buf, (u64)data_size, ret == -1i32 ? 0u64 : (u64)ret); $*/
                        free(buf);
                        goto socket_read_error;
                    }

#ifndef CN_ENV
                    /*$ extract Owned<uint8_t>, (u64)data_size; $*/
                    measure(buf, buf + data_size);
#else
                    // TODO this is a just-past-the-end pointer, difficulties with these in CN atm
                    measure(buf, buf + 0);
#endif
                    free(buf);
                }
                break;
            case 2:
                // Attest
                {
                    uint8_t nonce[NONCE_SIZE];
                    /*$ extract Block<uint8_t>, 0u64; $*/
                    uint8_t *nonce_0 = (uint8_t*)nonce;
                    ret = read_exact(socket_fd, nonce, sizeof(nonce));
                    if (ret != sizeof(nonce)) {
                        /*$ apply ForgetPartialInit_u8(nonce_0, (u64)NONCE_SIZE(), ret == -1i32 ? 0u64 : (u64)ret); $*/
                        goto socket_read_error;
                    }

                    uint8_t output[MEASURE_SIZE + HMAC_SIZE];
                    /*$ extract Block<uint8_t>, 0u64; $*/
                    uint8_t *output_0 = &output[0];
                    /*$ extract Block<uint8_t>, MEASURE_SIZE(); $*/
                    uint8_t *output_MEASURE_SIZE = &output[MEASURE_SIZE];
                    /*$ apply SplitAt_Block_u8(output_0, MEASURE_SIZE() + HMAC_SIZE(), MEASURE_SIZE(), HMAC_SIZE()); $*/
                    /*$ apply ViewShift_Block_u8(output_0, output_MEASURE_SIZE, MEASURE_SIZE(), HMAC_SIZE()); $*/
                    attest(nonce, &output[0], &output[MEASURE_SIZE]);
                    /*$ apply UnViewShift_Owned_u8(output_0, output_MEASURE_SIZE, MEASURE_SIZE(), HMAC_SIZE()); $*/
                    /*$ apply UnSplitAt_Owned_u8(output_0, MEASURE_SIZE() + HMAC_SIZE(), MEASURE_SIZE(), HMAC_SIZE()); $*/

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

int parse_hex_char(char c)
/*$
  // @PropertyClass: P1-LAC
  requires true;
  ensures (c == 0u8) ? (return == -1i32) : true;
    return >= -1i32;
    return < 16i32;
$*/
{
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

int parse_hex_str(const char* str, uint8_t* dest, size_t dest_size)
/*$
  // @PropertyClass: P3-SOP
  // @PropertyClass: P6-UserDefPred
  requires
    take stri = Stringa(str);
    take desti = ArrayBlock_u8(dest, dest_size);
  ensures
    return == 0i32 || return == -1i32;
    take destobad = CondArraySliceBlock_u8(dest, return == -1i32, 0u64, dest_size);
    take destook = CondArraySliceOwned_u8(dest, return == 0i32, 0u64, dest_size);
    take stro = Stringa(str);
    // This equality is very hard to carry though these string reference
    // manipulations without either very good array slice equality or
    // carrying it through each manipulation explicitly
    //TODO stri == stro;
$*/
{
    const char* cur = str;
    for (size_t i = 0; i < dest_size; i++)
    /*$ inv
      i <= dest_size;
      i*2u64 == (u64) cur - (u64) str;
      take destb = ArraySliceBlock_u8(dest, i, dest_size);
      take desto = ArraySliceOwned_u8(dest, 0u64, i);
      take sb = Str_Seg_Back(cur, i*2u64);
      take rest = Stringa(cur);
      {str} unchanged;
      {dest} unchanged;
      {dest_size} unchanged;
    $*/
    {
        // `strtol` is quite lenient in the input formats it accepts (e.g.
        // `+0xff` is the same as `ff`), which we don't want.

        // If the string `str` is too short, we'll end up calling
        // `parse_hex_char('\0')` and bailing out immediately after.
        int x1 = parse_hex_char(*cur);
        if (x1 < 0) {
            /*$ apply ForgetPartialInit_u8(dest, dest_size, i); $*/
            /*$ apply String_Iter_Finish(str, cur); $*/
            return -1;
        }
        int x2 = parse_hex_char(*(cur + 1));
        if (x2 < 0) {
            /*$ apply ForgetPartialInit_u8(dest, dest_size, i); $*/
            /*$ apply String_Iter_Finish(str, cur); $*/
            return -1;
        }
        /*$ apply Str_Seg_Back_twice(cur, i*2u64); $*/
        cur += 2;

        /*$ extract Block<uint8_t>, i; $*/
        /*$ extract Owned<uint8_t>, i; $*/
        dest[i] = (x1 << 4) | x2;

    }
    /*$ apply String_Iter_Finish(str, cur); $*/

    return 0;
}

int main(int argc, char *argv[])
/*$

  // @PropertyClass: P3-SOP
  accesses binary_path;
  accesses binary_fd;
  accesses boot_once;
  accesses current_measure;
  accesses __stderr;
  requires argc >= 0i32;
    take argvi = each (u64 i; i >= 0u64 && i < (u64)argc) {StringaRef(array_shift<char*>(argv,i))};
  ensures
    take argvo = each (u64 i; i >= 0u64 && i < (u64)argc) {StringaRef(array_shift<char*>(argv,i))};
$*/
{
    if (argc != 2 && argc != 3) {
        fprintf(stderr, "usage: %s binary [expected_hash]\n",
            argc >= 1 ? argv[0] : "trusted_boot");
        return 1;
    }

    /*$ extract StringaRef, 1u64; $*/
    binary_path = argv[1];

    const char* expected_measure_str = NULL;
    uint8_t expected_measure[MEASURE_SIZE];
    int ret = -1;
    if (argc >= 3) {
        /*$ extract StringaRef, 2u64; $*/
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

    if (st.st_size <= 0) {
        fprintf(stderr, "binary '%s' is empty\n", binary_path);
        return 1;
    }

    void* start = mmap(NULL, st.st_size, PROT_READ, MAP_SHARED, binary_fd, 0);
    if (start == MAP_FAILED) {
        perror("failed to mmap binary");
        return 1;
    }


#ifndef CN_ENV
   boot(start, ((uint8_t*)start) + st.st_size,
        expected_measure_str != NULL ? expected_measure : NULL,
        linux_run);
#else
   /*$ extract Owned<uint8_t>, 0u64; $*/
   boot(start, ((uint8_t*)start) + 0,
        expected_measure_str != NULL ? expected_measure : NULL,
        linux_run);
   munmap(start, st.st_size);
#endif

}
