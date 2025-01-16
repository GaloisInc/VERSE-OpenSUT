#ifndef CN_ARRAY_UTILS_H_
#define CN_ARRAY_UTILS_H_

/*$
predicate (map<u64,u8>) ArrayOrNull_u8 (pointer p, u64 l)
{
  if (!is_null(p)) {
    take pv = each(u64 i; i >= 0u64 && i < l) {Owned<uint8_t>(array_shift<uint8_t>(p,i))};
    return pv;
  } else {
    return default<map<u64,u8> >;
  }
}

predicate (map<u64,u8>) ArrayOrNull_Block_u8 (pointer p, u64 l)
{
  if (!is_null(p)) {
    take pv = each(u64 i; i >= 0u64 && i < l) {Block<uint8_t>(array_shift<uint8_t>(p,i))};
    return pv;
  } else {
    return default<map<u64,u8> >;
  }
}

lemma SplitAt_Block_u8(pointer tmp, u64 len, u64 at, u64 slen)
  requires
    take a1 = each(u64 j; 0u64<=j && j<len){Block<uint8_t>(array_shift<uint8_t>(tmp, j))};
    at >= 0u64;
    len >= 0u64;
    slen >= 0u64;
    at < len;
    slen <= len;
    at + slen <= len;
  ensures
    take a2 = each(u64 j; 0u64<=j && j<at){Block<uint8_t>(array_shift<uint8_t>(tmp, j))};
    take a3 = each(u64 j; ((u64)at)<=j && j<(at+slen)){Block<uint8_t>(array_shift<uint8_t>(tmp, j))};
    take a4 = each(u64 j; ((u64)(at+slen))<=j && j<len){Block<uint8_t>(array_shift<uint8_t>(tmp, j))};

lemma SplitAt_Owned_u8(pointer tmp, u64 len, u64 at, u64 slen)
  requires
    take a1 = each(u64 j; 0u64<=j && j<len){Owned<uint8_t>(array_shift<uint8_t>(tmp, j))};
    at >= 0u64;
    len >= 0u64;
    slen >= 0u64;
    at < len;
    slen <= len;
    at + slen <= len;
  ensures
    take a2 = each(u64 j; 0u64<=j && j<at){Owned<uint8_t>(array_shift<uint8_t>(tmp, j))};
    take a3 = each(u64 j; ((u64)at)<=j && j<(at+slen)){Owned<uint8_t>(array_shift<uint8_t>(tmp, j))};
    take a4 = each(u64 j; ((u64)(at+slen))<=j && j<len){Owned<uint8_t>(array_shift<uint8_t>(tmp, j))};

lemma UnSplitAt_Block_u8(pointer tmp, u64 len, u64 at, u64 slen)
  requires
    take a2 = each(u64 j; 0u64<=j && j<at){Block<uint8_t>(array_shift<uint8_t>(tmp, j))};
    take a3 = each(u64 j; ((u64)at)<=j && j<(at+slen)){Block<uint8_t>(array_shift<uint8_t>(tmp, j))};
    take a4 = each(u64 j; ((u64)(at+slen))<=j && j<len){Block<uint8_t>(array_shift<uint8_t>(tmp, j))};
    at >= 0u64;
    len >= 0u64;
    slen >= 0u64;
    at < len;
    slen <= len;
    at + slen <= len;
  ensures
    take a1 = each(u64 j; 0u64<=j && j<len){Block<uint8_t>(array_shift<uint8_t>(tmp, j))};

lemma UnSplitAt_Owned_u8(pointer tmp, u64 len, u64 at, u64 slen)
  requires
    take a2 = each(u64 j; 0u64<=j && j<at){Owned<uint8_t>(array_shift<uint8_t>(tmp, j))};
    take a3 = each(u64 j; ((u64)at)<=j && j<(at+slen)){Owned<uint8_t>(array_shift<uint8_t>(tmp, j))};
    take a4 = each(u64 j; ((u64)(at+slen))<=j && j<len){Owned<uint8_t>(array_shift<uint8_t>(tmp, j))};
    at >= 0u64;
    len >= 0u64;
    slen >= 0u64;
    at < len;
    slen <= len;
    at + slen <= len;
  ensures
    take a1 = each(u64 j; 0u64<=j && j<len){Owned<uint8_t>(array_shift<uint8_t>(tmp, j))};

lemma ViewShift_Block_u8(pointer a, pointer b, u64 at, u64 len)
  requires
    take a1 = each(u64 j; at <= j && j <(at+len)) {Block<uint8_t>(array_shift<uint8_t>(a,j))};
    ptr_eq(array_shift<uint8_t>(b,0u64), array_shift<uint8_t>(a,at));
  ensures
    take a2 = each(u64 j; 0u64 <= j && j <len) {Block<uint8_t>(array_shift<uint8_t>(b,j))};

lemma ViewShift_Owned_u8(pointer a, pointer b, u64 at, u64 len)
  requires
    take a1 = each(u64 j; at <= j && j <(at+len)) {Owned<uint8_t>(array_shift<uint8_t>(a,j))};
    ptr_eq(array_shift<uint8_t>(b,0u64), array_shift<uint8_t>(a,at));
  ensures
    take a2 = each(u64 j; 0u64 <= j && j <len) {Owned<uint8_t>(array_shift<uint8_t>(b,j))};

lemma UnViewShift_Block_u8(pointer a, pointer b, u64 at, u64 len)
  requires
    take a2 = each(u64 j; 0u64 <= j && j <len) {Block<uint8_t>(array_shift<uint8_t>(b,j))};
    ptr_eq(array_shift<uint8_t>(b,0u64), array_shift<uint8_t>(a,at));
  ensures
    take a1 = each(u64 j; at <= j && j <(at+len)) {Block<uint8_t>(array_shift<uint8_t>(a,j))};

// TODO this lemma takes an absolute start and end rather than an absolute start
// and a length. This should show in the name.
lemma UnViewShift_Block_At_u8(pointer a, pointer b, u64 oset, u64 s, u64 e)
  requires
    take a2 = each(u64 j; s <= j && j < e) {Block<uint8_t>(array_shift<uint8_t>(b,j))};
    ptr_eq(array_shift<uint8_t>(b,0u64), array_shift<uint8_t>(a,oset));
  ensures
    take a1 = each(u64 j; (oset + s) <= j && j <(oset+e)) {Block<uint8_t>(array_shift<uint8_t>(a,j))};


lemma UnViewShift_Owned_u8(pointer a, pointer b, u64 at, u64 len)
  requires
    take a2 = each(u64 j; 0u64 <= j && j <len) {Owned<uint8_t>(array_shift<uint8_t>(b,j))};
    ptr_eq(array_shift<uint8_t>(b,0u64), array_shift<uint8_t>(a,at));
  ensures
    take a1 = each(u64 j; at <= j && j <(at+len)) {Owned<uint8_t>(array_shift<uint8_t>(a,j))};

predicate (map<u64,u8>) ArrayBlock_u8 (pointer p, u64 e)
{
  take pv = each(u64 i; i >= 0u64 && i < e) {Block<uint8_t>(array_shift<uint8_t>(p,i))};
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
    take pv = each(u64 i; i >= s && i < e) {Block<uint8_t>(array_shift<uint8_t>(p,i))};
    return pv;
  } else {
    return default<map<u64,u8> >;
  }
}

predicate (map<u64,u8>) CondArraySliceOwned_u8 (pointer p, boolean c, u64 s, u64 e)
{
  if (c) {
    take pv = each(u64 i; i >= s && i < e) {Owned<uint8_t>(array_shift<uint8_t>(p,i))};
    return pv;
  } else {
    return default<map<u64,u8> >;
  }
}

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
    take aio = each(u64 i; i >= 0u64 && i < ol) {Owned<uint8_t>(array_shift<uint8_t>(a,i))};
    take aib = each(u64 i; i >= ol && i < l) {Block<uint8_t>(array_shift<uint8_t>(a,i))};
  ensures
    take aob = each(u64 i; i >= 0u64 && i < l) {Block<uint8_t>(array_shift<uint8_t>(a,i))};
$*/

#endif // CN_ARRAY_UTILS_H_
