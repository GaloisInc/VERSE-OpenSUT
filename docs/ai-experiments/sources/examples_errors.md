# Example CN errors and solutions

## Array Load

Broken file:

```C
int read (int *p, int n, int i)
/*@ requires take A = each(i32 j; 0i32 <= j && j < n) { 
                        Owned<int>(array_shift<int>(p,j)) };
             0i32 <= i && i < n; 
    ensures take A_post = each(i32 j; 0i32 <= j && j < n) { 
                        Owned<int>(array_shift<int>(p,j)) }; 
@*/
{
  return p[i];
}
```

Error:
```
array_load.broken.c:2:19: warning: 'each' expects a 'u64', but 'j' with type 'i32' was provided. This will become an error in the future.
/*@ requires take A = each(i32 j; 0i32 <= j && j < n) { 
                  ^
array_load.broken.c:5:18: warning: 'each' expects a 'u64', but 'j' with type 'i32' was provided. This will become an error in the future.
    ensures take A_post = each(i32 j; 0i32 <= j && j < n) { 
                 ^
[1/1]: read -- fail
array_load.broken.c:9:10: error: `&p[(u64)i]` out of bounds
  return p[i];
         ^~~~ 
(UB missing short message): UB_CERB004_unspecified__pointer_add
```

Fix #1:
```C
int read (int *p, int n, int i)
/*@ requires take A = each(i32 j; 0i32 <= j && j < n) { 
                        Owned<int>(array_shift<int>(p,j)) };
             0i32 <= i && i < n; 
    ensures take A_post = each(i32 j; 0i32 <= j && j < n) { 
                        Owned<int>(array_shift<int>(p,j)) }; 
@*/
{
  /*@ extract Owned<int>, i; @*/
  return p[i];
}
```

Fix #2:
```
int read (int *p, int n, int i)
/*@ requires take a1 = each(i32 j; 0i32 <= j && j < n) { Owned<int>(array_shift<int>(p,j)) };
             0i32 <= i && i < n;
    ensures take a2 = each(i32 j; 0i32 <= j && j < n) { Owned<int>(array_shift<int>(p,j)) };
            a1 == a2;
            return == a1[i];
@*/
{
  /*@ extract Owned<int>, i; @*/
  return p[i];
}
```

## Read

Broken file:

```C
int read (int *p)
/*@ requires take v1 = Owned<int>(p); @*/
{
  return *p;
}

```

Error:
```
[1/1]: read -- fail
read.broken.c:4:3: error: Left-over unused resource 'Owned<signed int>(p)(v1)'
  return *p;
  ^~~~~~~~~~ 

```

Fix #1:
```C
int read (int *p)

/*@ requires take P = Owned<int>(p);
    ensures take P_post = Owned<int>(p);
@*/

{
  return *p;
}

```

Fix #2:
```C
int read (int *p)
/*@ requires take P = Owned<int>(p);
    ensures take P_post = Owned<int>(p);
            return == P;
            P_post == P;
@*/
{
  return *p;
}

```

## Signed Increment

Broken file:

```C
void incr (int *p)
/*@ requires take v1 = Block<int>(p);
    ensures take v2 = Owned<int>(p);
            v2 == v1+1i32; @*/
{
  int n = *p;
  int m = n+1;
  *p = m;
}

```

Error:
```
[1/1]: incr -- fail
slf0_incr.broken.c:8:11: error: Missing resource for reading
  int n = *p;
          ^~ 
Resource needed: Owned<signed int>(p)
```

Fix #1:
```C
void incr (int *p)
/*@ requires take v1 = Owned<int>(p);
    requires let N = (i64) v1;
             (i64)MINi32() <= N - 1i64; N + 1i64 <= (i64)MAXi32();
             (i64)MINi32() <= N + N; N + N <= (i64)MAXi32();
    ensures take v2 = Owned<int>(p);
            v2 == v1+1i32; @*/
{
  int n = *p;
  int m = n+1;
  *p = m;
}

```


## Transpose

Broken file:

```C
struct point { int x; int y; };

void transpose (struct point *p) 
/*@ requires take P = Owned<struct point>(p);
    ensures take P_post = Owned<struct point>(p);
            P_post.x == P.y;
            P_post.y == P.x;
@*/
{
  int temp_x = p->x;
  int temp_y = p->y;
  /*@ assert(false); @*/
  p->x = temp_y;
  p->y = temp_x;
}

```

Error:
```
[1/1]: transpose -- fail
transpose.broken.c:12:7: error: Unprovable constraint
  /*@ assert(false); @*/
      ^~~~~~~~~~~~~~ 
Constraint from transpose.broken.c:12:7:
  /*@ assert(false); @*/
      ^~~~~~~~~~~~~~ 

```

Fix #1:
```C
struct point { int x; int y; };

void transpose (struct point *p) 
/*@ requires take P = Owned<struct point>(p);
    ensures take P_post = Owned<struct point>(p);
            P_post.x == P.y;
            P_post.y == P.x;
@*/
{
  int temp_x = p->x;
  int temp_y = p->y;
  p->x = temp_y;
  p->y = temp_x;
}

```


Fix #2:
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

struct upoint { unsigned int x; unsigned int y; };

void transpose2 (struct upoint *p)

/*@ requires take P = Owned<struct upoint>(p);
    ensures take P_post = Owned<struct upoint>(p);
            P_post.x == P.y;
            P_post.y == P.x;
@*/

{
  swap(&p->x, &p->y);
}

```