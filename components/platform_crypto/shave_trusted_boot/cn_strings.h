#ifndef CN_STRINGS_H_
#define CN_STRINGS_H_

/*$

datatype strf {
  Strf_E {},
  Strf_NE { u8 head, datatype strf tail }
}
predicate (datatype strf) StringaRef(pointer r)
{
  take p = Owned<char*>(r);
  take h = Owned<char>(p);
  take s = Stringa_Aux(p, h);
  assert (h != 0u8 || s == Strf_E { } );
  return s;
}

predicate (datatype strf) Stringa(pointer p)
{
  take h = Owned<char>(p);
  take s = Stringa_Aux(p, h);
  assert (h != 0u8 || s == Strf_E { } );
  return s;
}

predicate (datatype strf) Stringa_Aux (pointer p, u8 h)
{
  if (h == 0u8) {
    return Strf_E { };
  }
  else {
    take t = Stringa(array_shift<char>(p, 1u64));
    return Strf_NE { head : h, tail : t };
  }
}

$*/

#endif // CN_STRINGS_H_
