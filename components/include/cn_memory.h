#ifndef CN_MEMCPY_H_
#define CN_MEMCPY_H_

#ifdef WAR_CN_358
#include <posix/sys/types.h>
#else
#include <sys/types.h>
#endif

void *memset(void *dest, int v, size_t n);
/*$
spec memset(pointer dest, i32 v, u64 n);
  // @PropertyClass: P3-SOP
  // TODO possibly P9 full functional correctness here, although no ghost state
requires
    take Dest = each (u64 i; 0u64 <= i && i < n ) { Block<unsigned char>(array_shift<unsigned char>(dest, i)) };

ensures
    take DestR = each (u64 i; 0u64 <= i && i < n ) { Owned<unsigned char>(array_shift<unsigned char>(dest, i)) };
    each (u64 i; 0u64 <= i && i < n ) { DestR[i] == (u8)v };
    ptr_eq(return, dest);
$*/

int _memcmp(const unsigned char *dest, const unsigned char *src, size_t n);
/*$ spec _memcmp(pointer dest, pointer src, u64 n);
  // @PropertyClass: P3-SOP
  // TODO also full functional correctness?
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
  // @PropertyClass: P3-SOP
  // TODO also full functional correctness?
requires
    take Src = each (u64 i; 0u64 <= i && i < n ) { Owned(array_shift(src, i)) };
    take Dest = each (u64 i; 0u64 <= i && i < n ) { Block<unsigned char>(array_shift(dest, i)) };

ensures
    take SrcR = each (u64 i; 0u64 <= i && i < n ) { Owned(array_shift(src, i)) };
    take DestR = each (u64 i; 0u64 <= i && i < n ) { Owned(array_shift(dest, i)) };
    Src == SrcR;
    each (u64 i; 0u64 <= i && i < n ) { SrcR[i] == DestR[i] };
$*/

/*$ spec memchr(pointer s, i32 c, size_t n);
  // @PropertyClass: P3-SOP
  // TODO also full functional correctness
  requires
    c >= 0i32;
    take sin = each(u64 i; i < (u64) n) {Owned<uint8_t>(array_shift<uint8_t>(s, i))};
  ensures
    take sout = each(u64 i; i < (u64) n) {Owned<uint8_t>(array_shift<uint8_t>(s, i))};
    is_null(return) || (return >= s && return < array_shift<uint8_t>(s, n));
$*/

void _free(void *p);
/*$
spec _free(pointer p);
  // @PropertyClass: P3-SOP
  // TODO also full functional correctness?
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
  // @PropertyClass: P3-SOP
  // TODO also full functional correctness?
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

datatype OptionMemoryOwned {
    SomeMemoryO {{u64 base, u64 size} al, map<u64, u8> ow},
    NoneMemoryO {}
}

datatype OptionMemoryPartial {
    SomeMemoryP {{u64 base, u64 size} al, map<u64, u8> ow, map<u64, u8> bl},
    NoneMemoryP {}
}

// Predicate representing the result of a malloc() that can fail. Either 
// NoneMemory if it fails, or SomeMemory if it succeeds 
predicate (datatype OptionMemory) MallocResult(pointer p, u64 n)
  // @PropertyClass: P3-SOP
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
  // @PropertyClass: P3-SOP
  // @PropertyClass: P6-UserDefPred
  // TODO also full functional correctness?
requires true;
ensures  take Out = MallocResult(return, n);
$*/

/*$
predicate (datatype OptionMemory) GetLineArgsAux(pointer p, size_t cc)
  // @PropertyClass: P3-SOP
{
  if (is_null(p)) {
    return NoneMemory {};
  } else {
    take log = Alloc(p);
    assert(allocs[(alloc_id)p] == log);
    assert(log.base == (u64) p);
    assert(cc == log.size);
    take i = each(u64 j; j >= 0u64 && j < log.size) {Block<uint8_t>(array_shift<uint8_t>(p, j))};
    return SomeMemory { al : log, bu : i};
  }
}

predicate (datatype OptionMemory) GetLineArgs(pointer p, pointer c)
  // @PropertyClass: P3-SOP
  // @PropertyClass: P6-UserDefPred
{
  take pp = Owned<char*>(p);
  take cc = Owned<size_t>(c);
  take k = GetLineArgsAux(pp, cc);
  return k;
}

predicate (datatype OptionMemoryPartial) GetLineResultAux(pointer pp, size_t cc, ssize_t ret)
  // @PropertyClass: P3-SOP
{
  if (ret == -1i64) {
    assert(is_null(pp));
    return NoneMemoryP {};
  } else {
    take log = Alloc(pp);
    assert(allocs[(alloc_id)pp] == log);
    assert(log.base == (u64) pp);
    assert(cc == log.size);
    take io = each(u64 j; j >= 0u64 && j < (u64)ret) {Owned<uint8_t>(array_shift<uint8_t>(pp, j))};
    take ib = each(u64 j; j >= (u64)ret && j < log.size) {Block<uint8_t>(array_shift<uint8_t>(pp, j))};
    return SomeMemoryP { al : log, ow : io, bl : ib};
  }
}

predicate (datatype OptionMemoryPartial) GetLineResult(pointer p, pointer c, ssize_t ret)
  // @PropertyClass: P3-SOP
  // @PropertyClass: P6-UserDefPred
{
  take pp = Owned<char*>(p);
  take cc = Owned<size_t>(c);
  assert(ret >= -1i64);
  assert(ret <= (i64)cc);
  take k = GetLineResultAux(pp, cc, ret);
  return k;
}
$*/

void *_realloc(void *ptr, size_t size);

/*$
predicate (datatype OptionMemoryOwned) OptionAllocatedString(pointer p)
  // @PropertyClass: P3-SOP
{
  if (is_null(p)) {
    return NoneMemoryO {};
  } else {
    take log = Alloc(p);
    assert(allocs[(alloc_id)p] == log);
    assert(log.base == (u64) p);
    take i = each(u64 j; j >= 0u64 && j < log.size) {Owned<uint8_t>(array_shift<uint8_t>(p, j))};
    return SomeMemoryO { al : log, ow : i};
  }
}
$*/


#endif // CN_MEMCPY_H_
