#ifndef CN_MEMCPY_H_
#define CN_MEMCPY_H_

int _memcmp(const unsigned char *dest, const unsigned char *src, size_t n);
/*$ spec _memcmp(pointer dest, pointer src, u64 n);

requires
    take Src = each (u64 i; 0u64 <= i && i < n ) { Owned(array_shift(src, i)) };
    take Dest = each (u64 i; 0u64 <= i && i < n ) { Owned(array_shift(dest, i)) };

ensures
    take SrcR = each (u64 i; 0u64 <= i && i < n ) { Owned(array_shift(src, i)) };
    take DestR = each (u64 i; 0u64 <= i && i < n ) { Owned(array_shift(dest, i)) };
    Src == SrcR; Dest == DestR;
    (return != 0i32 || Src == Dest) && (return == 0i32 || Src != Dest);
$*/

void _memcpy(unsigned char *dest,
                 const unsigned char *src, size_t n);
/*$
spec _memcpy(pointer dest, pointer src, u64 n);
requires
    take Src = each (u64 i; 0u64 <= i && i < n ) { Owned(array_shift(src, i)) };
    take Dest = each (u64 i; 0u64 <= i && i < n ) { Block<unsigned char>(array_shift(dest, i)) };

ensures
    take SrcR = each (u64 i; 0u64 <= i && i < n ) { Owned(array_shift(src, i)) };
    take DestR = each (u64 i; 0u64 <= i && i < n ) { Owned(array_shift(dest, i)) };
    Src == SrcR;
    each (u64 i; 0u64 <= i && i < n ) { SrcR[i] == DestR[i] };
$*/

#endif // CN_MEMCPY_H_
