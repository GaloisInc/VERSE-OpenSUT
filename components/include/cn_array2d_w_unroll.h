#ifndef CN_ARRAY2D_W_UNROLL_H_
#define CN_ARRAY2D_W_UNROLL_H_

/*$
predicate (map<u64,map<u64,u8> >) ArrayW2_u8(pointer p, u64 m, u64 n)
{
  assert(n < 5u64);
  assert(n > 1u64);
  take pv = ArrayW2_u8_5(p, m, n);
  return pv;
}
predicate (map<u64,map<u64,u8> >) ArrayW2_u8_5(pointer p, u64 m, u64 n)
{
  if (n == 5u64) {
    take pv = each(u64 i; i >= 0u64 && i < m) {W<uint8_t[5]>(array_shift<uint8_t[5]>(p,i))};
    return pv;
  } else {
    take pv = ArrayW2_u8_4(p, m, n);
    return pv;
  }
}
predicate (map<u64,map<u64,u8> >) ArrayW2_u8_4(pointer p, u64 m, u64 n)
{
  if (n == 4u64) {
    take pv = each(u64 i; i >= 0u64 && i < m) {W<uint8_t[4]>(array_shift<uint8_t[4]>(p,i))};
    return pv;
  } else {
    take pv = ArrayW2_u8_3(p, m, n);
    return pv;
  }
}
predicate (map<u64,map<u64,u8> >) ArrayW2_u8_3(pointer p, u64 m, u64 n)
{
  if (n == 3u64) {
    take pv = each(u64 i; i >= 0u64 && i < m) {W<uint8_t[3]>(array_shift<uint8_t[3]>(p,i))};
    return pv;
  } else {
    take pv = ArrayW2_u8_2(p, m, n);
    return pv;
  }
}
predicate (map<u64,map<u64,u8> >) ArrayW2_u8_2(pointer p, u64 m, u64 n)
{
  if (n == 2u64) {
    take pv = each(u64 i; i >= 0u64 && i < m) {W<uint8_t[2]>(array_shift<uint8_t[2]>(p,i))};
    return pv;
  } else {
    take pv = ArrayW2_u8_1(p, m, n);
    return pv;
  }
}
predicate (map<u64,map<u64,u8> >) ArrayW2_u8_1(pointer p, u64 m, u64 n)
{
  assert(n == 1u64);
  take pv = each(u64 i; i >= 0u64 && i < m) {W<uint8_t[1]>(array_shift<uint8_t[1]>(p,i))};
  return pv;
}
$*/

#endif // CN_ARRAY2D_W_UNROLL_H_
