#ifndef CN_MEMCPY_H_
#define CN_MEMCPY_H_

void *memset(void *dest, int v, size_t n);
/*$
spec memset(pointer dest, i32 v, u64 n);
requires
    take Dest = each (u64 i; 0u64 <= i && i < n ) { Block<unsigned char>(array_shift<unsigned char>(dest, i)) };

ensures
    take DestR = each (u64 i; 0u64 <= i && i < n ) { Owned<unsigned char>(array_shift<unsigned char>(dest, i)) };
    each (u64 i; 0u64 <= i && i < n ) { DestR[i] == (u8)v };
    ptr_eq(return, dest);
$*/

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

void _free(void *p);
/*$
spec _free(pointer p);
requires
    !is_null(p);
    take log = Alloc(p);
    allocs[(alloc_id)p] == log;
    let base = array_shift<char>(p, 0u64);
    log.base == (u64) base;
    take i = each(u64 j; j >= 0u64 && j < log.size) {Block<uint8_t>(array_shift<uint8_t>(p, j))};
ensures
    true;
$*/

void *_malloc(size_t n);
/*$
spec _malloc(u64 n);
requires true;
ensures
    !is_null(return);
    take log = Alloc(return);
    allocs[(alloc_id)return] == log;
    log.base == (u64) return;
    log.size == n;
    take i = each(u64 j; j >= 0u64 && j < n) {Block<uint8_t>(array_shift<uint8_t>(return, j))};
$*/

/*$
// Option type used in MallocResult() predicate to represent the result of a 
// malloc() call that can fail. This can be removed once CN supports a real 
// Option type 
datatype OptionMemory {
    SomeMemory {{u64 base, u64 size} al, map<u64, u8> bu}, 
    NoneMemory {}
}

// Predicate representing the result of a malloc() that can fail. Either 
// NoneMemory if it fails, or SomeMemory if it succeeds 
predicate (datatype OptionMemory) MallocResult(pointer p, u64 n)
{
  if (is_null(p)) {
    return NoneMemory {}; 
  } else {
    take log = Alloc(p);
    assert(allocs[(alloc_id)p] == log);
    assert(log.base == (u64) p);
    assert(log.size == n);
    take i = each(u64 j; j >= 0u64 && j < n) {Block<uint8_t>(array_shift<uint8_t>(p, j))};
    return SomeMemory { al : log, bu : i};
  }
}
$*/

// Specification for a malloc() that can fail. Generates a MallocResult() 
// in memory 
void *_malloc_canfail(size_t n);
/*$
spec _malloc_canfail(u64 n);
requires true;
ensures  take Out = MallocResult(return, n);
$*/

void *_realloc(void *ptr, size_t size);

#endif // CN_MEMCPY_H_
