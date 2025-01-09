# Example CN programs

File abs.c

```C
int abs (int x)

/*@ requires MINi32() < x;
    ensures return == ((x >= 0i32) ? x : (0i32-x));
@*/

{
  if (x >= 0) {
    return x;
  } else {
    return -x;
  }
}
```

File abs_mem.c

```C
int abs_mem (int *p)

/*@ requires take x = Owned<int>(p);
             MINi32() < x;
    ensures take x_post = Owned<int>(p);
            x == x_post;
            return == ((x >= 0i32) ? x : (0i32-x));
@*/

{
  int x = *p;
  if (x >= 0) {
    return x;
  }
  else {
    return -x;
  }
}
```

File abs_mem_struct.c

```C
int abs_mem (int *p)

/*@ requires take x = Owned<int>(p);
             MINi32() < x;
    ensures take x2 = Owned<int>(p);
            x == x2;
            return == ((x >= 0i32) ? x : (0i32-x));
@*/

{
  int x = *p;
  if (x >= 0) {
    return x;
  }
  else {
    return -x;
  }
}



struct tuple {
  int x;
  int y;
};


int abs_y (struct tuple *p)
/*@ requires take s = Owned(p);
             MINi32() < s.y;
    ensures  take s2 = Owned(p);
             s == s2;
             return == ((s.y >= 0i32) ? s.y : (0i32-s.y));
@*/
{
  return abs_mem(&p->y);
}
```

File add_0.c

```C
int add(int x, int y)

/*@ requires let Sum = (i64) x + (i64) y;
             -2147483648i64 <= Sum; Sum <= 2147483647i64; @*/

{
  return x+y;
}
```

File add_1.c

```C
int add(int x, int y)

/*@ requires let Sum = (i64) x + (i64) y;
             -2147483648i64 <= Sum; Sum <= 2147483647i64;
    ensures return == (i32) Sum;
@*/

{
  return x+y;
}
```

File add_2.c

```C
int add(int x, int y)

/*@ requires let Sum = (i64) x + (i64) y;
             (i64)MINi32() <= Sum; Sum <= (i64)MAXi32();
    ensures return == (i32) Sum;
@*/

{
  return x+y;
}
```

File add_read.c

```C
unsigned int add (unsigned int *p, unsigned int *q)
/*@ requires take P = Owned<unsigned int>(p);
             take Q = Owned<unsigned int>(q);
    ensures take P_post = Owned<unsigned int>(p);
            take Q_post = Owned<unsigned int>(q);
            P == P_post && Q == Q_post;
            return == P + Q;
@*/
{
  unsigned int m = *p;
  unsigned int n = *q;
  return m+n;
}
```

File add_two_array.c

```C
unsigned int array_read_two (unsigned int *p, int n, int i, int j)

/*@ requires take A = each(i32 k; 0i32 <= k && k < n) { 
                        Owned<unsigned int>(array_shift<unsigned int>(p,k)) };
             0i32 <= i && i < n;
             0i32 <= j && j < n;
             j != i;
    ensures take A_post = each(i32 k; 0i32 <= k && k < n) { 
                            Owned<unsigned int>(array_shift<unsigned int>(p,k)) };
            A == A_post;
            return == A[i] + A[j];
@*/

{

  /*@ extract Owned<unsigned int>, i; @*/

  unsigned int tmp1 = p[i];

  /*@ extract Owned<unsigned int>, j; @*/

  unsigned int tmp2 = p[j];
  return (tmp1 + tmp2);
}
```

File bcp_framerule.c

```C
void incr_first (unsigned int *p, unsigned int *q)
/*@ requires take pv = Owned<unsigned int>(p);
    ensures take pv_ = Owned<unsigned int>(p);
            pv_ == pv + 1u32;
@*/
{
  unsigned int n = *p;
  unsigned int m = n+1;
  *p = m;
}

void incr_first_frame (unsigned int *p, unsigned int *q)
/*@ requires take pv = Owned<unsigned int>(p);
             take qv = Owned<unsigned int>(q);
    ensures take pv_ = Owned<unsigned int>(p);
            take qv_ = Owned<unsigned int>(q);
            pv_ == pv + 1u32;
            qv_ == qv;
@*/
{
  incr_first(p, q);
}
```

File const_example.c

```C
#define CONST 1
    /*@ function (i32) CONST () @*/
    static int c_CONST() /*@ cn_function CONST; @*/ { return CONST; }

int foo (int x)
/*@
  requires true;
  ensures return == CONST();
@*/
{
  return CONST;
}
```

File const_example_lessgood.c

```C
#define CONST 1
/*@ function (i32) CONST () { 1i32 } @*/
```

File init_array2.c

```C
void init_array2 (char *p, unsigned int n)
/*@ requires take A = each(u32 i; i < n) { 
                        Block<char>( array_shift<char>(p, i)) };
    ensures  take A_post = each(u32 i; i < n) { 
                             Owned<char>( array_shift<char>(p, i)) };
@*/
{
  unsigned int j = 0;
  while (j < n)

  /*@ inv take Al = each(u32 i; i < j) { 
                      Owned<char>( array_shift<char>(p, i)) };
          take Ar = each(u32 i; j <= i && i < n) { 
                      Block<char>( array_shift<char>(p, i)) };
          {p} unchanged; {n} unchanged;
          j <= n;
  @*/

  {

    /*@ extract Block<char>, j; @*/
    /*@ extract Owned<char>, j; @*/

    p[j] = 0;
    j++;
  }
}
```

File init_array.c

```C
void init_array (char *p, unsigned int n)
/*@ requires take A = each(u32 i; i < n) { 
                         Owned<char>( array_shift<char>(p, i)) };
    ensures  take A_post = each(u32 i; i < n) { 
                             Owned<char>( array_shift<char>(p, i)) };
@*/
{
  unsigned int j = 0;
  while (j < n)

  /*@ inv take Ai = each(u32 i; i < n) { 
                      Owned<char>( array_shift<char>(p, i)) };
          {p} unchanged; 
          {n} unchanged;
  @*/

  {

    /*@ extract Owned<char>, j; @*/

    p[j] = 0;
    j++;
  }
}
```

File init_array_rev.c

```C
void init_array_rev (char *p, unsigned int n)
/*@ requires take A = each(u32 i; i < n) { 
                        Block<char>( array_shift<char>(p, i)) };
    n > 0u32;
    ensures  take A_post = each(u32 i; i < n) { 
                             Owned<char>( array_shift<char>(p, i)) };
@*/
{
  unsigned int j = 0;
  while (j < n)

  /*@ inv take Al = each(u32 i; i < n-j) { 
                      Block<char>( array_shift<char>(p, i)) };
          take Ar = each(u32 i; n-j <= i && i < n) { 
                      Owned<char>( array_shift<char>(p, i)) };
          {p} unchanged; {n} unchanged;
          0u32 <= j && j <= n;
  @*/

  {

    /*@ extract Block<char>, n-(j+1u32); @*/
    /*@ extract Owned<char>, n-(j+1u32); @*/

    p[n-(j+1)] = 0;
    j++;
  }
}
```

File init_point.c

```C
void zero (int *coord) 
/*@ requires take Coord = Block<int>(coord);
    ensures take Coord_post = Owned<int>(coord);
            Coord_post == 0i32; @*/
{
  *coord = 0;
}

struct point { int x; int y; };

void init_point(struct point *p) 
/*@ requires take P = Block<struct point>(p);
    ensures take P_post = Owned<struct point>(p);
            P_post.x == 0i32;
            P_post.y == 0i32;
@*/
{
  zero(&p->x);
  zero(&p->y);
}
```

File slf10_basic_ref.c

```C
extern unsigned int *refUnsignedInt (unsigned int v);
/*@ spec refUnsignedInt(u32 v);
    requires true;
    ensures take vr = Owned(return);
            vr == v;
@*/

```

File slf11_basic_ref_greater.c

```C
#include "slf10_basic_ref.c"

unsigned int *ref_greater (unsigned int *p)

/*@ requires take n1 = Owned(p);
    ensures  take n2 = Owned(p);
             take m2 = Owned(return);
             n2 == n1;
             m2 == n1 + 1u32;
@*/

{
  unsigned int n = *p;
  unsigned int m = n+1;
  return refUnsignedInt(m);
}
```

File slf12_basic_ref_greater_abstract.c

```C
#include "slf10_basic_ref.c"

unsigned int *ref_greater (unsigned int *p)

/*@ requires take n1 = Owned(p);
             n1 < n1 + 1u32;
    ensures  take n2 = Owned(p);
             take m2 = Owned(return);
             n2 == n1;
             m2 > n1;
@*/

{
  unsigned int n = *p;
  unsigned int m = n+1;
  return refUnsignedInt(m);
}
```

File slf15_basic_succ_using_incr_attempt_.c

```C
/* triple_succ_using_incr_attempt'  cannot be expressed in CN */

```

File slf16_basic_succ_using_incr.c

```C
#include "free.h"
#include "ref.h"
#include "slf0_basic_incr.c"

unsigned int succ_using_incr (unsigned int n)
/*@ ensures return == n + 1u32; @*/
{
  unsigned int *p = refUnsignedInt(n);
  incr(p);
  unsigned int x = *p;
  freeUnsignedInt(p);
  return x;
}
```

File slf17_get_and_free.c

```C
#include "free.h"

unsigned int get_and_free (unsigned int *p)
/*@ requires take P = Owned(p);
    ensures return == P; 
@*/
{
  unsigned int v = *p;
  freeUnsignedInt (p);
  return v;
}
```

File slf18_two_dice.c

```C
unsigned int val_rand (unsigned int n);
/*@ spec val_rand(u32 n);
    requires n > 0u32;
    ensures 0u32 <= return && return < n;
@*/

unsigned int two_dice ()
/*@ ensures 2u32 <= return && return <= 12u32; @*/
{
  unsigned int n1 = val_rand (6);
  unsigned int n2 = val_rand (6);
  unsigned int s = n1 + n2;
  return s + 2;
}
```

File slf1_basic_example_let.c

```C
unsigned int example_let (unsigned int n) 
/*@ ensures return == 2u32 * n;
@*/
{
  unsigned int a = n+1;
  unsigned int b = n-1;
  return a+b;
}


```

File slf1_basic_example_let.signed.c

```C
int doubled (int n)

/*@ requires let N = (i64) n;
             (i64)MINi32() <= N - 1i64; N + 1i64 <= (i64)MAXi32();
             (i64)MINi32() <= N + N; N + N <= (i64)MAXi32();
    ensures return == n * 2i32;
@*/

{
  int a = n+1;
  int b = n-1;
  return a+b;
}
```

File slf2_basic_quadruple.c

```C
unsigned int quadruple (unsigned int n)
/*@ ensures return == 4u32 * n; @*/
{
  unsigned int m = n + n;
  return m + m;
}
```

File slf2_basic_quadruple.signed.c

```C
int quadruple (int n)

/*@ requires let N = (i64) n;
             (i64)MINi32() <= N * 4i64; N * 4i64 <= (i64)MAXi32();
    ensures return == 4i32 * n;
 @*/

{
  int m = n + n;
  return m + m;
}
```

File slf3_basic_inplace_double.c

```C
void inplace_double (int *p)

/*@ requires take P = Owned<int>(p);
             let M = 2i64 * ((i64) P);
             (i64) MINi32() <= M; M <= (i64) MAXi32();
    ensures  take P_post = Owned<int>(p);
             P_post == (i32) M;
@*/

{
  int n = *p;
  int m = n + n;
  *p = m;
}
```

File slf7_basic_incr_first.c

```C
#include "slf0_basic_incr.c"

void incr_first(unsigned int *p, unsigned int *q)
/*@ requires take n1 = Owned(p);
             take m1 = Owned(q);
    ensures  take n2 = Owned(p);
             take m2 = Owned(q);
             n2 == n1 + 1u32;
             m2 == m1;
@*/
{
  incr(p);
}


void incr_first_(unsigned int *p, unsigned int *q)
/*@ requires take n1 = Owned(p);
    ensures  take n2 = Owned(p);
             n2 == n1 + 1u32;
@*/
{
  incr(p);
}
```

File slf8_basic_transfer.c

```C
void transfer (unsigned int *p, unsigned int *q)

/*@ requires take P = Owned(p);
             take Q = Owned(q);
    ensures  take P_post = Owned(p);
             take Q_post = Owned(q);
             P_post == P + Q;
             Q_post == 0u32;
@*/

{
  unsigned int n = *p;
  unsigned int m = *q;
  unsigned int s = n + m;
  *p = s;
  *q = 0;
}
```

File slf9_basic_transfer_aliased.c

```C
void transfer (unsigned int *p, unsigned int *q)
/*@ requires take n1 = Owned(p);
             ptr_eq(p,q);
    ensures  take n2 = Owned(p);
             n2 == 0u32;
@*/
{
  unsigned int n = *p;
  unsigned int m = *q;
  unsigned int s = n + m;
  *p = s;
  *q = 0;
}
```

File slf_incr2_alias.c

```C
// Increment two different pointers (same as above)
void incr2a (unsigned int *p, unsigned int *q)
/*@ requires take P = Owned<unsigned int>(p);
             take Q = Owned<unsigned int>(q);
    ensures take P_post = Owned<unsigned int>(p);
            take Q_post = Owned<unsigned int>(q);
            P_post == P + 1u32;
            Q_post == Q + 1u32;
@*/
{
  unsigned int n = *p;
  unsigned int m = n+1;
  *p = m;
  n = *q;
  m = n+1;
  *q = m;
}

// Increment the same pointer twice
void incr2b (unsigned int *p, unsigned int *q)
/*@ requires take P = Owned<unsigned int>(p);
             ptr_eq(q,p);
    ensures take P_post = Owned<unsigned int>(p);
            ptr_eq(q,p);
            P_post == P + 2u32;
@*/
{
  unsigned int n = *p;
  unsigned int m = n+1;
  *p = m;
  n = *q;
  m = n+1;
  *q = m;
}

void call_both (unsigned int *p, unsigned int *q)
/*@ requires take pv = Owned<unsigned int>(p);
             take qv = Owned<unsigned int>(q);
    ensures take pv_ = Owned<unsigned int>(p);
            take qv_ = Owned<unsigned int>(q);
            pv_ == pv + 3u32;
            qv_ == qv + 1u32;
@*/
{
  incr2a(p, q);   // increment two different pointers
  incr2b(p, p);   // increment the same pointer twice
}
```

File slf_incr2.c

```C
/*@
predicate { u32 P, u32 Q } BothOwned (pointer p, pointer q)
{
  if (ptr_eq(p,q)) {
    take PX = Owned<unsigned int>(p);
    return {P: PX, Q: PX};
  }
  else {
    take PX = Owned<unsigned int>(p);
    take QX = Owned<unsigned int>(q);
    return {P: PX, Q: QX};
  }
}
@*/

void incr2(unsigned int *p, unsigned int *q)
/*@ requires take PQ = BothOwned(p,q);
    ensures take PQ_post = BothOwned(p,q);
            PQ_post.P == (!ptr_eq(p,q) ? (PQ.P + 1u32) : (PQ.P + 2u32));
            PQ_post.Q == (!ptr_eq(p,q) ? (PQ.Q + 1u32) : PQ_post.P);
@*/
{
  /*@ split_case ptr_eq(p,q); @*/
  unsigned int n = *p;
  unsigned int m = n + 1;
  *p = m;
  n = *q;
  m = n + 1;
  *q = m;
}

void call_both_better(unsigned int *p, unsigned int *q)
/*@ requires take P = Owned<unsigned int>(p);
             take Q = Owned<unsigned int>(q);
             !ptr_eq(p,q);
    ensures take P_post = Owned<unsigned int>(p);
            take Q_post = Owned<unsigned int>(q);
            P_post == P + 3u32;
            Q_post == Q + 1u32;
@*/
{
  incr2(p, q);
  incr2(p, p);
}
```

File slf_incr2_noalias.c

```C
void incr2a (unsigned int *p, unsigned int *q)
/*@ requires take P = Owned<unsigned int>(p);
             take Q = Owned<unsigned int>(q);
    ensures take P_post = Owned<unsigned int>(p);
            take Q_post = Owned<unsigned int>(q);
            P_post == P + 1u32;
            Q_post == Q + 1u32;
@*/
{
  unsigned int n = *p;
  unsigned int m = n+1;
  *p = m;
  n = *q;
  m = n+1;
  *q = m;
}

```

File slf_quadruple_mem.c

```C
int quadruple_mem (int *p)

/*@ requires take P = Owned<int>(p);
             let P64 = (i64) P;
             (i64)MINi32() <= P64 * 4i64; P64 * 4i64 <= (i64)MAXi32();
    ensures take P_post = Owned<int>(p);
            P_post == P;
            return == 4i32 * P;
 @*/

{
  int m = *p + *p;
  return m + m;
}
```

File slf_ref_greater.c

```C
#include "malloc.h"

unsigned int *ref_greater_abstract (unsigned int *p)

/*@ requires take P = Owned<unsigned int>(p);
             P < 4294967295u32;
    ensures take P_post = Owned<unsigned int>(p);
            take R = Owned<unsigned int>(return);
            P == P_post;
            P <= R;
@*/

{
  unsigned int* q = mallocUnsignedInt();
  *q = *p + 1;
  return q;
}
```

File swap_array.c

```C
void swap_array (int *p, int n, int i, int j)

/*@ requires take a1 = each(i32 k; 0i32 <= k && k < n) { Owned<int>(array_shift<int>(p,k)) };
             0i32 <= i && i < n;
             0i32 <= j && j < n;
             j != i;
    ensures take a2 = each(i32 k; 0i32 <= k && k < n) { Owned<int>(array_shift<int>(p,k)) };
            a2 == a1[i: a1[j], j: a1[i]];
@*/

{

  /*@ extract Owned<int>, i; @*/

  int tmp = p[i];

  /*@ extract Owned<int>, j; @*/

  p[i] = p[j];
  p[j] = tmp;
}
```

File swap.c

```C
void swap (unsigned int *p, unsigned int *q)

/*@ requires take P = Owned<unsigned int>(p);
             take Q = Owned<unsigned int>(q);
    ensures  take P_post = Owned<unsigned int>(p);
             take Q_post = Owned<unsigned int>(q);
             P_post == Q && Q_post == P;
@*/

{
  unsigned int m = *p;
  unsigned int n = *q;
  *p = n;
  *q = m;
}
```

File zero.c

```C
void zero (int *p)

/*@ requires take P = Block<int>(p);
    ensures take P_post = Owned<int>(p);
            P_post == 0i32;
@*/

{
  *p = 0;
}
```

