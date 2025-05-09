#ifndef CN_MATH_H_
#define CN_MATH_H_

#include <stdbool.h>
#include <stdint.h>

bool __builtin_sadd_overflow (int a, int b, int *res);
/*$ spec __builtin_sadd_overflow(i32 a, i32 b, pointer res);
  // @PropertyClass: P1-LAC
  // @PropertyClass: P3-SOP
    requires take x = Block<int>(res);
    ensures take out = Owned<int>(res);
      (return == (1u8)) || (out == (a + b));
$*/
bool __builtin_smul_overflow (int a, int b, int *res);
/*$ spec __builtin_smul_overflow(i32 a, i32 b, pointer res);
  // @PropertyClass: P1-LAC
  // @PropertyClass: P3-SOP
    requires take x = Block<int>(res);
    ensures take out = Owned<int>(res);
      (return == (1u8)) || (out == (a * b));
$*/
bool __builtin_ssub_overflow (int a, int b, int *res);
/*$ spec __builtin_ssub_overflow(i32 a, i32 b, pointer res);
  // @PropertyClass: P1-LAC
  // @PropertyClass: P3-SOP
    requires take x = Block<int>(res);
    ensures take out = Owned<int>(res);
      (return == (1u8)) || (out == (a - b));
$*/
bool __builtin_saddll_overflow (int64_t a, int64_t b, int64_t *res);
/*$ spec __builtin_saddll_overflow(i64 a, i64 b, pointer res);
  // @PropertyClass: P1-LAC
  // @PropertyClass: P3-SOP
    requires take x = Block<int64_t>(res);
    ensures take out = Owned<int64_t>(res);
      (return == (1u8)) || (out == (a + b));
$*/
bool __builtin_smulll_overflow (int64_t a, int64_t b, int64_t *res);
/*$ spec __builtin_smulll_overflow(i64 a, i64 b, pointer res);
  // @PropertyClass: P1-LAC
  // @PropertyClass: P3-SOP
    requires take x = Block<int64_t>(res);
    ensures take out = Owned<int64_t>(res);
      (return == (1u8)) || (out == (a * b));
$*/
bool __builtin_ssubll_overflow (int64_t a, int64_t b, int64_t *res);
/*$ spec __builtin_ssubll_overflow(i64 a, i64 b, pointer res);
  // @PropertyClass: P1-LAC
  // @PropertyClass: P3-SOP
    requires take x = Block<int64_t>(res);
    ensures take out = Owned<int64_t>(res);
      (return == (1u8)) || (out == (a - b));
$*/

#endif // CN_MATH_H_
