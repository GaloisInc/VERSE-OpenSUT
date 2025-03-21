#ifndef CN_STRINGS_H_
#define CN_STRINGS_H_

/*$

datatype strf {
  Strf_E {},
  Strf_NE { u8 head, datatype strf tail }
}

datatype str_seg_back {
  StrSegBack_E {},
  StrSegBack_NE { datatype str_seg_back tail, u8 head }
}

predicate (datatype strf) StringaRef(pointer r)
  // @PropertyClass: P3-SOP
  // @PropertyClass: P6-UserDefPred
{
  take p = Owned<char*>(r);
  take h = Owned<char>(p);
  take s = Stringa_Aux(p, h);
  assert (h != 0u8 || s == Strf_E { } );
  return s;
}

predicate (datatype strf) Stringa(pointer p)
  // @PropertyClass: P3-SOP
  // @PropertyClass: P6-UserDefPred
{
  take h = Owned<char>(p);
  take s = Stringa_Aux(p, h);
  assert (h != 0u8 || s == Strf_E { } );
  return s;
}

predicate (datatype strf) Stringa_Aux (pointer p, u8 h)
  // @PropertyClass: P3-SOP
  // @PropertyClass: P6-UserDefPred
{
  if (h == 0u8) {
    return Strf_E { };
  }
  else {
    take t = Stringa(array_shift<char>(p, 1u64));
    return Strf_NE { head : h, tail : t };
  }
}

// TODO this is modified from the upstream, it doesn't own s[0] which makes it
// easier to pair Stringa(s) and Str_Seg_Back(s, n)
predicate (datatype str_seg_back) Str_Seg_Back(pointer s, u64 len) {
  // @PropertyClass: P6-UserDefPred
  take tl = Str_Seg_Back_Aux(array_shift<char>(s, -1i64), len);
  return tl;
}

predicate (datatype str_seg_back) Str_Seg_Back_Aux(pointer s, u64 len) {
  // @PropertyClass: P3-SOP
  // @PropertyClass: P6-UserDefPred
  if (len == 0u64) {
    return StrSegBack_E { };
  }
  else {
    take h = Owned<char>(s);
    take tl = Str_Seg_Back_Aux(array_shift<char>(s, -1i64), len - 1u64);
    return StrSegBack_NE { tail : tl, head: h };
  }
}

lemma String_Iter_Finish(pointer start, pointer cursor)
  // @PropertyClass: P6-UserDefPred
  requires
    take sc = Stringa(cursor);
    take spre = Str_Seg_Back(cursor, ((u64)cursor)-((u64)start));
  ensures
    take s = Stringa(start);
$*/

/*$
// TODO this seems like it should be possible to do with a simple hint or pack command or something
lemma Str_Seg_Back_twice(pointer start, u64 len)
  // @PropertyClass: P3-SOP
  requires
    take spre = Str_Seg_Back(start, len);
    take sa = Owned<char>(array_shift<char>(start,0u64));
    take sb = Owned<char>(array_shift<char>(start,1u64));
  ensures
    take s = Str_Seg_Back(array_shift<char>(start,2u64), len+2u64);
$*/

#endif // CN_STRINGS_H_
