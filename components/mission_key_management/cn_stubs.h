#pragma once

// From `sys/epoll.h`
#define EPOLLIN 1
#define EPOLLOUT 4


// From `stdio.h`

/*$ spec fprintf(pointer f, pointer s);
requires true;
ensures true;
$*/

#ifndef WAR_CN_309
// not possible to call this due to CN issue #309
// this spec isn't right but can't develop it at all without #309
void perror(const char *msg);
/*$ 
spec perror(pointer msg);
requires 
    take mi = Owned<char>(msg);
ensures 
    take mo = Owned<char>(msg);
    mi == mo;
$*/
#else
# define perror(...) 0
#endif
/*$ spec exit(i32 v);
    requires true;
    ensures true;
$*/



// From `unistd.h`

// // Old version, updated by MDD below 
// ssize_t _read(int fildes, void *buf, size_t n);
// /*$ spec _read(i32 fildes, pointer buf, u64 n);
//     // accesses errno;
//     requires
//       take bufi = ArrayBlock_u8(buf, n);
//     ensures
//      return >= -1i64 && return <= (i64)n;
//      // return == -1 -> no owned, all block
//      // return >= 0 < n -> 0 <= owned < return, return <= block < n
//      // return == n -> 0 <= owned < n, return <= block < n
//      take bufo = each(u64 i; (return == -1i64) ? false : (0u64 <= i && i <(u64)return)) {Owned<uint8_t>(array_shift<uint8_t>(buf, i))};
//      take bufb = each(u64 i; (return == -1i64) ? (0u64 <= i && i < n) : ((u64)return <= i && i < n)) {Block<uint8_t>(array_shift<uint8_t>(buf, i))};
// $*/

ssize_t _read_uint8_t(int fildes, void *buf, size_t n);
/*$ 
spec _read_uint8_t(i32 fildes, pointer buf, u64 n);
requires
    take buf_in = each (u64 i; i < n) { Owned<uint8_t>(array_shift<uint8_t>(buf, i))}; 
ensures
    return >= -1i64 && return <= (i64)n;
    take buf_out = each (u64 i; i < n) { Owned<uint8_t>(array_shift<uint8_t>(buf, i))}; 
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

#define memcpy(d,s,n) _memcpy(d,s,n)
#define memcmp(s1,s2,n) _memcmp(s1,s2,n)
#define malloc(x) _malloc(x)
#define free(x) _free(x)
