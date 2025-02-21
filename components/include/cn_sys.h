#ifndef CN_SYS_H_
#define CN_SYS_H_
#include "cn_array_utils.h"

ssize_t _read(int fildes, void *buf, size_t n);
/*$ spec _read(i32 fildes, pointer buf, u64 n);
    requires
      take bufi = ArrayBlock_u8(buf, n);
    ensures
     return >= -1i64 && return <= (i64)n;
     // return == -1 -> no owned, all block
     // return >= 0 < n -> 0 <= owned < return, return <= block < n
     // return == n -> 0 <= owned < n, return <= block < n
     take bufo = each(u64 i; (return <= -1i64) ? false : (0u64 <= i && i <(u64)return)) {Owned<uint8_t>(array_shift<uint8_t>(buf, i))};
     take bufb = each(u64 i; (return <= -1i64) ? (0u64 <= i && i < n) : ((u64)return <= i && i < n)) {Block<uint8_t>(array_shift<uint8_t>(buf, i))};
$*/
ssize_t _write(int fildes, const void *buf, size_t nbyte);
/*$ spec _write(i32 fildes, pointer buf, u64 nbyte);
  requires
    ((i32)nbyte) >= 0i32;
    take bufi = each(u64 i; i >= 0u64 && i < nbyte) {Owned<uint8_t>(array_shift<uint8_t>(buf,i))};
  ensures
    take bufo = each(u64 i; i >= 0u64 && i < nbyte) {Owned<uint8_t>(array_shift<uint8_t>(buf,i))};
    bufi == bufo;
    return >= -1i64 && return < (i64)nbyte;
$*/

#define read(f,b,s) _read(f,b,s)
#define write(f,b,s) _write(f,b,s)

#endif // CN_SYS_H_
