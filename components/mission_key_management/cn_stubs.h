#pragma once

// Provides substitutes for some declarations that CN has trouble with.


// Cerberus puts some POSIX headers under the `posix/` directory.
#include <posix/sys/types.h>
#include "policy.h"

// From `sys/epoll.h`
#define EPOLLIN 1
#define EPOLLOUT 4

// From `sys/socket.h`
#define SHUT_RDWR 2

// From `policy.h`

// This is the idiomatic CN lifting of macro constants, per 
// https://rems-project.github.io/cn-tutorial/getting-started/style-guide/?h=constant

/*$ function (u64) KEY_ID_SIZE () $*/
static uint64_t c_KEY_ID_SIZE() /*$ cn_function KEY_ID_SIZE; $*/ { return KEY_ID_SIZE; }
/*$ function (u64) NONCE_SIZE () $*/
static uint64_t c_NONCE_SIZE() /*$ cn_function NONCE_SIZE; $*/ { return NONCE_SIZE; }
/*$ function (u64) MEASURE_SIZE () $*/
static uint64_t c_MEASURE_SIZE() /*$ cn_function MEASURE_SIZE; $*/ { return MEASURE_SIZE; }
/*$ function (u64) HMAC_SIZE () $*/
static uint64_t c_HMAC_SIZE() /*$ cn_function HMAC_SIZE; $*/ { return HMAC_SIZE; }
/*$ function (u64) HMAC_KEY_SIZE () $*/
static uint64_t c_HMAC_KEY_SIZE() /*$ cn_function HMAC_KEY_SIZE; $*/ { return HMAC_KEY_SIZE; }
/*$ function (u64) KEY_SIZE () $*/
static uint64_t c_KEY_SIZE() /*$ cn_function KEY_SIZE; $*/ { return KEY_SIZE; }

// Non-deterministically return a pointer to a key, or NULL 
const uint8_t* policy_match(uint8_t key_id[KEY_ID_SIZE], uint8_t nonce[NONCE_SIZE],
        uint8_t measure[MEASURE_SIZE], uint8_t hmac[HMAC_SIZE]);
/*$ spec policy_match(pointer key_id, pointer nonce, pointer measure, pointer hmac); 
requires 
    true; 
ensures 
    take Key_out = KeyPred(return); 
$*/

// Ghost function which releases the memory representing a key. Implicitly, this
// is returning ownership of the memory to whatever internal state manages the
// key list. 
void key_release (const uint8_t *key); 
/*$ spec key_release(pointer key); 
requires 
    take Key_in = KeyPred(key);
ensures 
    true; 
$*/

// From `stdio.h`

/*$ spec fprintf(pointer f, pointer s);
requires true;
ensures true;
$*/

#ifndef WAR_CN_309
// not possible to call this due to CN issue #309
// this spec isn't right but can't develop it at all without #309
void perror(const char *msg);
/*$ spec perror(pointer msg);
    requires take mi = Owned<char>(msg);
    ensures take mo = Owned<char>(msg);
    mi == mo;
$*/
#else
# define perror(...) 0
#endif
/*$ spec exit(i32 v);
    requires true;
    ensures true;
$*/

// #define fprintf(...) 0
// #define snprintf(...) 0


// From `unistd.h`

ssize_t _read_uint8_t(int fildes, void *buf, size_t n);
/*$ 
spec _read_uint8_t(i32 fildes, pointer buf, u64 n);
requires
    take buf_in = each (u64 i; i < n) { Owned<uint8_t>(array_shift<uint8_t>(buf, i))}; 
ensures
    return >= -1i64 && return <= (i64)n;
    take buf_out = each (u64 i; i < n) { Owned<uint8_t>(array_shift<uint8_t>(buf, i))}; 
    buf_out == buf_in; 
$*/
#define read(f,b,s) _read_uint8_t(f,b,s)

int _close(int fildes);
/*$ 
spec _close(i32 fildes);
requires true;
ensures true;
$*/
#define close(x) _close(x)

ssize_t _write_uint8_t(int fildes, const void *buf, size_t nbyte);
/*$ 
spec _write_uint8_t(i32 fildes, pointer buf, u64 nbyte);
requires
    ((i32)nbyte) >= 0i32;
    take bufi = each(u64 i; i < nbyte) {Owned<uint8_t>(array_shift<uint8_t>(buf,i))};
ensures
    take bufo = each(u64 i; i < nbyte) {Owned<uint8_t>(array_shift<uint8_t>(buf,i))};
    bufi == bufo;
    return >= -1i64 && return < (i64)nbyte;
$*/
#define write(f,b,s) _write_uint8_t(f,b,s)

int _shutdown(int fildes, int how);
/*$ spec _shutdown(i32 fildes, i32 how);
    requires true;
    ensures true;
$*/
#define shutdown(x,h) _shutdown(x,h)

#define memcpy(d,s,n) _memcpy(d,s,n)
#define memcmp(s1,s2,n) _memcmp(s1,s2,n)
#define malloc(x) _malloc(x)
#define free(x) _free(x)


// void *_memcpy_uint8_t(void *dest, const void *src, size_t nbyte);
// /*$
// spec _memcpy_uint8_t(pointer dest, pointer src, u64 nbyte); 
// requires 
//     ((i32)nbyte) >= 0i32;
//     take src_in  = each (u64 i; i < nbyte) { Owned<uint8_t>(array_shift<uint8_t>(src,i)) }; 
//     take dest_in = each (u64 i; i < nbyte) { Owned<uint8_t>(array_shift<uint8_t>(dest,i)) }; 
// ensures
//     take src_out  = each (u64 i; i < nbyte) { Owned<uint8_t>(array_shift<uint8_t>(src,i)) }; 
//     take dest_out = each (u64 i; i < nbyte) { Owned<uint8_t>(array_shift<uint8_t>(dest,i)) }; 
//     src_in == src_out; 
//     // TODO: is this the right behavior?  
//     if (is_null(return)) {
//         dest_out == dest_in 
//     } else {
//         ptr_eq(return, dest) 
//         && 
//         dest_out == src_out
//     };
// $*/
// #define memcpy(d,s,n) _memcpy_uint8_t(d,s,n) 

// int _memcmp_uint8_t(const void *s1, const void *s2, size_t nbyte);
// /*$
// spec _memcmp_uint8_t(pointer s1, pointer s2, u64 nbyte); 
// requires 
//     ((i32)nbyte) >= 0i32;
//     take S1_in = each (u64 i; i < nbyte) { Owned<uint8_t>(array_shift<uint8_t>(s1,i)) }; 
//     take S2_in = each (u64 i; i < nbyte) { Owned<uint8_t>(array_shift<uint8_t>(s2,i)) }; 
// ensures 
//     take S1_out = each (u64 i; i < nbyte) { Owned<uint8_t>(array_shift<uint8_t>(s1,i)) }; 
//     take S2_out = each (u64 i; i < nbyte) { Owned<uint8_t>(array_shift<uint8_t>(s2,i)) }; 
//     S1_out == S1_in; S2_out == S2_in; 
//     if (S1_in == S2_in) { return > 0i32 } else { return == 0i32 }; 
// $*/
// #define memcmp(s1,s2,n) _memcmp_uint8_t(s1,s2,n)

// struct client *_malloc_struct_client(size_t nbyte); 
// /*$ 
// spec _malloc_struct_client(u64 nbyte); 
// requires 
//     ((i32)nbyte) >= 0i32; 
// ensures 
//     take Client_out = Owned<struct client>(return); 
// $*/
// #define malloc(n) _malloc_struct_client(n)

// void _free_struct_client(struct client *target); 
// /*$ 
// spec _free_struct_client(pointer target); 
// requires 
//     take Client_out = Owned<struct client>(target); 
// ensures 
//     true; 
// $*/
// #define free(t) _free_struct_client(t)
