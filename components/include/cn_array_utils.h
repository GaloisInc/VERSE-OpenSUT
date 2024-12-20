#ifndef CN_ARRAY_UTILS_H_
#define CN_ARRAY_UTILS_H_

/*$
predicate (map<u64,u8>) ArrayBlock_u8 (pointer p, u64 e)
{
  take pv = each(u64 i; i >= 0u64 && i < e) {Block<uint8_t>(array_shift<uint8_t>(p,i))};
  return pv;
}

predicate (map<u64,u8>) ArrayOwned_u8 (pointer p, u64 e)
{
  take pv = each(u64 i; i >= 0u64 && i < e) {Owned<uint8_t>(array_shift<uint8_t>(p,i))};
  return pv;
}

predicate (map<u64,u8>) ArraySliceBlock_u8 (pointer p, u64 s, u64 e)
{
  take pv = each(u64 i; i >= s && i < e) {Block<uint8_t>(array_shift<uint8_t>(p,i))};
  return pv;
}

predicate (map<u64,u8>) ArraySliceOwned_u8 (pointer p, u64 s, u64 e)
{
  take pv = each(u64 i; i >= s && i < e) {Owned<uint8_t>(array_shift<uint8_t>(p,i))};
  return pv;
}

predicate (map<u64,u8>) CondArraySliceBlock_u8 (pointer p, boolean c, u64 s, u64 e)
{
  if (c) {
    take pv = ArraySliceBlock_u8(p, s, e);
    return pv;
  } else {
    return default<map<u64,u8> >;
  }
}

predicate (map<u64,u8>) CondArraySliceOwned_u8 (pointer p, boolean c, u64 s, u64 e)
{
  if (c) {
    take pv = ArraySliceOwned_u8(p, s, e);
    return pv;
  } else {
    return default<map<u64,u8> >;
  }
}

predicate (map<u64,u8>) ArrayOrNull_u8 (pointer p, u64 l)
{
  if (!is_null(p)) {
    take pv = ArrayOwned_u8(p, l);
    return pv;
  } else {
    return default<map<u64,u8> >;
  }
}

predicate (map<u64,u8>) ArrayOrNull_Block_u8 (pointer p, u64 l)
{
  if (!is_null(p)) {
    take pv = ArrayBlock_u8(p, l);
    return pv;
  } else {
    return default<map<u64,u8> >;
  }
}

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

lemma ViewShift_Block_u8(pointer a, pointer b, u64 at, u64 len)
  requires
    take a1 = ArraySliceBlock_u8(a, at, at+len);
    ptr_eq(array_shift<uint8_t>(b,0u64), array_shift<uint8_t>(a,at));
  ensures
    take a2 = ArrayBlock_u8(b, len);

lemma ViewShift_Owned_u8(pointer a, pointer b, u64 at, u64 len)
  requires
    take a1 = ArraySliceOwned_u8(a, at, at+len);
    ptr_eq(array_shift<uint8_t>(b,0u64), array_shift<uint8_t>(a,at));
  ensures
    take a2 = ArrayOwned_u8(b, len);

lemma UnViewShift_Block_u8(pointer a, pointer b, u64 at, u64 len)
  requires
    take a2 = ArrayBlock_u8(b, len);
    ptr_eq(array_shift<uint8_t>(b,0u64), array_shift<uint8_t>(a,at));
  ensures
    take a1 = ArraySliceOwned_u8(a, at, at+len);

// TODO this lemma takes an absolute start and end rather than an absolute start
// and a length. This should show in the name.
lemma UnViewShift_Block_At_u8(pointer a, pointer b, u64 oset, u64 s, u64 e)
  requires
    take a2 = ArraySliceBlock_u8(b, s, e);
    ptr_eq(array_shift<uint8_t>(b,0u64), array_shift<uint8_t>(a,oset));
  ensures
    take a1 = ArraySliceBlock_u8(a, oset+s, oset+e);

lemma UnViewShift_Owned_u8(pointer a, pointer b, u64 at, u64 len)
  requires
    take a2 = ArrayOwned_u8(b, len);
    ptr_eq(array_shift<uint8_t>(b,0u64), array_shift<uint8_t>(a,at));
  ensures
    take a1 = ArraySliceOwned_u8(a, at, at+len);

lemma TransmuteArray_Block_u16_u8(pointer a, u64 l)
  requires
    take ai = each(u64 i; i >= 0u64 && i < l) {Block<uint16_t>(array_shift<uint16_t>(a,i))};
  ensures
    take ao = each(u64 i; i >= 0u64 && i < (2u64*l)) {Block<uint8_t>(array_shift<uint8_t>(a,i))};

lemma UnTransmuteArray_Block_u16_u8(pointer a, u64 l)
  requires
    take ai = each(u64 i; i >= 0u64 && i < (2u64*l)) {Block<uint8_t>(array_shift<uint8_t>(a,i))};
  ensures
    take ao = each(u64 i; i >= 0u64 && i < l) {Block<uint16_t>(array_shift<uint16_t>(a,i))};

lemma UnTransmuteArray_Owned_u16_u8(pointer a, u64 l)
  requires
    take ai = each(u64 i; i >= 0u64 && i < (2u64*l)) {Owned<uint8_t>(array_shift<uint8_t>(a,i))};
  ensures
    take ao = each(u64 i; i >= 0u64 && i < l) {Owned<uint16_t>(array_shift<uint16_t>(a,i))};

lemma ForgetPartialInit_u8(pointer a, u64 l, u64 ol)
  requires
    ol <= l;
    take aio = ArrayOwned_u8(a, ol);
    take aib = ArraySliceBlock_u8(a, ol, l);
  ensures
    take aob = ArrayBlock_u8(a, l);
$*/

#endif // CN_ARRAY_UTILS_H_
