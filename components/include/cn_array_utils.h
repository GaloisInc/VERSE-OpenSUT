#ifndef CN_ARRAY_UTILS_H_
#define CN_ARRAY_UTILS_H_

/*
These predicates are a mix of:
* syntactic sugar
* workarounds for the current requirement that CN specs never conditionally
  create a resource without a predicate.
* workarounds for the fact that CN does not equate x[2] and (&x[1])[1]
*/

/*$
//An uninitialized uint8_t array starting at p on indices [0, e)
predicate (map<u64,u8>) ArrayBlock_u8 (pointer p, u64 e)
{
  take pv = each(u64 i; i >= 0u64 && i < e) {W<uint8_t>(array_shift<uint8_t>(p,i))};
  return pv;
}

//An initialized uint8_t array starting at p on indices [0, e)
predicate (map<u64,u8>) ArrayOwned_u8 (pointer p, u64 e)
{
  take pv = each(u64 i; i >= 0u64 && i < e) {RW<uint8_t>(array_shift<uint8_t>(p,i))};
  return pv;
}

//An uninitialized slice of some uint8_t array starting at p on indices [s, e)
predicate (map<u64,u8>) ArraySliceBlock_u8 (pointer p, u64 s, u64 e)
{
  take pv = each(u64 i; i >= s && i < e) {W<uint8_t>(array_shift<uint8_t>(p,i))};
  return pv;
}

//An uninitialized slice of some uint8_t array starting at p on indices [s, e)
predicate (map<u64,u8>) ArraySliceOwned_u8 (pointer p, u64 s, u64 e)
{
  take pv = each(u64 i; i >= s && i < e) {RW<uint8_t>(array_shift<uint8_t>(p,i))};
  return pv;
}

//When condition c is true, an uninitialized slice of some uint8_t array
//starting at p on indices [s, e). Otherwise nothing.
predicate (map<u64,u8>) CondArraySliceBlock_u8 (pointer p, boolean c, u64 s, u64 e)
{
  if (c) {
    take pv = ArraySliceBlock_u8(p, s, e);
    return pv;
  } else {
    return default<map<u64,u8> >;
  }
}

//When condition c is true, an initialized slice of some uint8_t array
//starting at p on indices [s, e). Otherwise nothing.
predicate (map<u64,u8>) CondArraySliceOwned_u8 (pointer p, boolean c, u64 s, u64 e)
{
  if (c) {
    take pv = ArraySliceOwned_u8(p, s, e);
    return pv;
  } else {
    return default<map<u64,u8> >;
  }
}

//If p is not null, an initialized uint8_t array
//starting at p on indices [0, l). Otherwise nothing.
predicate (map<u64,u8>) ArrayOrNull_u8 (pointer p, u64 l)
{
  if (!is_null(p)) {
    take pv = ArrayOwned_u8(p, l);
    return pv;
  } else {
    return default<map<u64,u8> >;
  }
}

//If p is not null, an uninitialized uint8_t array
//starting at p on indices [0, l). Otherwise nothing.
predicate (map<u64,u8>) ArrayOrNull_Block_u8 (pointer p, u64 l)
{
  if (!is_null(p)) {
    take pv = ArrayBlock_u8(p, l);
    return pv;
  } else {
    return default<map<u64,u8> >;
  }
}

//Starting with an uninitialized uint8_t array at p with length len, cut out the
//slice [at, at+slen) from it, also creating the slices [0, at) and [at+slen,
//len).
lemma SplitAt_Block_u8(pointer tmp, u64 len, u64 at, u64 slen)
  requires
    take a1 = ArrayBlock_u8(tmp, len);
    at >= 0u64;
    len >= 0u64;
    slen >= 0u64;
    at < len;
    slen <= len;
    at + slen <= len;
  ensures
    take a2 = ArraySliceBlock_u8(tmp, 0u64, at);
    take a3 = ArraySliceBlock_u8(tmp, at, at+slen);
    take a4 = ArraySliceBlock_u8(tmp, at+slen, len);

//Starting with an initialized uint8_t array at p with length len, cut out the
//slice [at, at+slen) from it, also creating the slices [0, at) and [at+slen,
//len).
lemma SplitAt_Owned_u8(pointer tmp, u64 len, u64 at, u64 slen)
  requires
    take a1 = ArrayOwned_u8(tmp, len);
    at >= 0u64;
    len >= 0u64;
    slen >= 0u64;
    at < len;
    slen <= len;
    at + slen <= len;
  ensures
    take a2 = ArraySliceOwned_u8(tmp, 0u64, at);
    take a3 = ArraySliceOwned_u8(tmp, at, at+slen);
    take a4 = ArraySliceOwned_u8(tmp, at+slen, len);

// Call this lemma with the same arguments as SplitAt_Block_u8 to undo it.
lemma UnSplitAt_Block_u8(pointer tmp, u64 len, u64 at, u64 slen)
  requires
    take a2 = ArraySliceBlock_u8(tmp, 0u64, at);
    take a3 = ArraySliceBlock_u8(tmp, at, at+slen);
    take a4 = ArraySliceBlock_u8(tmp, at+slen, len);
    at >= 0u64;
    len >= 0u64;
    slen >= 0u64;
    at < len;
    slen <= len;
    at + slen <= len;
  ensures
    take a1 = ArrayBlock_u8(tmp, len);

// construct a slice at tmp [m,n) from slices [m,cut) and [cut,n)
lemma JoinSlice_Block_u8(pointer tmp, u64 m, u64 n, u64 cut)
  requires
    m <= cut;
    cut <= n;
    take a2 = ArraySliceBlock_u8(tmp, m, cut);
    take a3 = ArraySliceBlock_u8(tmp, cut, n);
  ensures
    take a1 = ArraySliceBlock_u8(tmp, m, n);

// Call this lemma with the same arguments as SplitAt_Owned_u8 to undo it.
lemma UnSplitAt_Owned_u8(pointer tmp, u64 len, u64 at, u64 slen)
  requires
    take a2 = ArraySliceOwned_u8(tmp, 0u64, at);
    take a3 = ArraySliceOwned_u8(tmp, at, at+slen);
    take a4 = ArraySliceOwned_u8(tmp, at+slen, len);
    at >= 0u64;
    len >= 0u64;
    slen >= 0u64;
    at < len;
    slen <= len;
    at + slen <= len;
  ensures
    take a1 = ArrayOwned_u8(tmp, len);

// construct a slice at tmp [m,n) from slices [m,cut) and [cut,n)
lemma JoinSlice_Owned_u8(pointer tmp, u64 m, u64 n, u64 cut)
  requires
    m <= cut;
    cut <= n;
    take a2 = ArraySliceOwned_u8(tmp, m, cut);
    take a3 = ArraySliceOwned_u8(tmp, cut, n);
  ensures
    take a1 = ArraySliceOwned_u8(tmp, m, n);

// CN does not automatically consider that a[1] and (&a[1])[0] are equal, so
// this lemma takes a uninitialized slice that has an initial offset and
// produces a new slice with a 0 initial offset.
lemma ViewShift_Block_u8(pointer a, pointer b, u64 at, u64 len)
  requires
    take a1 = ArraySliceBlock_u8(a, at, at+len);
    ptr_eq(array_shift<uint8_t>(b,0u64), array_shift<uint8_t>(a,at));
  ensures
    take a2 = ArrayBlock_u8(b, len);

// CN does not automatically consider that a[1] and (&a[1])[0] are equal, so
// this lemma takes a initialized slice that has an initial offset and
// produces a new slice with a 0 initial offset.
lemma ViewShift_Owned_u8(pointer a, pointer b, u64 at, u64 len)
  requires
    take a1 = ArraySliceOwned_u8(a, at, at+len);
    ptr_eq(array_shift<uint8_t>(b,0u64), array_shift<uint8_t>(a,at));
  ensures
    take a2 = ArrayOwned_u8(b, len);

// Call this with the same arguments as ViewShift_Block_u8 to undo it. Note that
// this could be implemented as ViewShift_Block(b, a, -at, len) if lemmas could
// make calls.
lemma UnViewShift_Block_u8(pointer a, pointer b, u64 at, u64 len)
  requires
    take a2 = ArrayBlock_u8(b, len);
    ptr_eq(array_shift<uint8_t>(b,0u64), array_shift<uint8_t>(a,at));
  ensures
    take a1 = ArraySliceBlock_u8(a, at, at+len);

// TODO this lemma takes an absolute start and end rather than an absolute start
// and a length. This should show in the name.
//
// This allows you to shift the origin of a slice with potentially both ends
// having a nonzero offset.
lemma UnViewShift_Block_At_u8(pointer a, pointer b, u64 oset, u64 s, u64 e)
  requires
    take a2 = ArraySliceBlock_u8(b, s, e);
    ptr_eq(array_shift<uint8_t>(b,0u64), array_shift<uint8_t>(a,oset));
  ensures
    take a1 = ArraySliceBlock_u8(a, oset+s, oset+e);

// Call this with the same arguments as ViewShift_Owned_u8 to undo it. Note that
// this could be implemented as ViewShift_Owned(b, a, -at, len) if lemmas could
// make calls.
lemma UnViewShift_Owned_u8(pointer a, pointer b, u64 at, u64 len)
  requires
    take a2 = ArrayOwned_u8(b, len);
    ptr_eq(array_shift<uint8_t>(b,0u64), array_shift<uint8_t>(a,at));
  ensures
    take a1 = ArraySliceOwned_u8(a, at, at+len);

// Turn an uninitialized uint16_t array resource into an uninitialized uint8_t
// resource. You can now use the to_bytes statement in CN for this.
lemma TransmuteArray_Block_u16_u8(pointer a, u64 l)
  requires
    take ai = each(u64 i; i >= 0u64 && i < l) {W<uint16_t>(array_shift<uint16_t>(a,i))};
  ensures
    take ao = each(u64 i; i >= 0u64 && i < (2u64*l)) {W<uint8_t>(array_shift<uint8_t>(a,i))};

// Turn an uninitialized uint8_t array resource into an uninitialized uint16_t
// resource. You can now use the from_bytes statement in CN for this.
lemma UnTransmuteArray_Block_u16_u8(pointer a, u64 l)
  requires
    take ai = each(u64 i; i >= 0u64 && i < (2u64*l)) {W<uint8_t>(array_shift<uint8_t>(a,i))};
  ensures
    take ao = each(u64 i; i >= 0u64 && i < l) {W<uint16_t>(array_shift<uint16_t>(a,i))};

// Turn an initialized uint8_t array into an initialized uint16_t array into a
// uint16_t array, forgetting information about the values.
lemma UnTransmuteArray_Owned_u16_u8(pointer a, u64 l)
  requires
    take ai = each(u64 i; i >= 0u64 && i < (2u64*l)) {RW<uint8_t>(array_shift<uint8_t>(a,i))};
  ensures
    take ao = each(u64 i; i >= 0u64 && i < l) {RW<uint16_t>(array_shift<uint16_t>(a,i))};

// Take two resources representing an array partially initialized in a segment
// starting at index 0 and return one resource representing an uninitialized
// array.
lemma ForgetPartialInit_u8(pointer a, u64 l, u64 ol)
  requires
    ol <= l;
    take aio = ArrayOwned_u8(a, ol);
    take aib = ArraySliceBlock_u8(a, ol, l);
  ensures
    take aob = ArrayBlock_u8(a, l);
$*/

#endif // CN_ARRAY_UTILS_H_
