#pragma once

// CN-compatible stubs for libc functions we use.

#include <sys/types.h>

#include <time.h>
// Additional functions that are missing from CN's `time.h`
void tzset(void);
size_t strftime(char *s, size_t max,
        const char *restrict format, const struct tm *restrict tm);
struct tm *localtime_r(const time_t *restrict timep,
        struct tm *restrict result);


// From `stdio.h`

#ifndef WAR_CN_309
// not possible to call this due to CN issue #309
// this spec isn't right but can't develop it at all without #309
void perror(const char *msg);
/*$ spec perror(pointer msg);
    requires take mi = Owned<char>(msg);
    ensures take mo = Owned<char>(msg);
      mi == mo;
$*/
#else
# define perror(...) 0
#endif

#define printf(...) 0
#define vsnprintf(...) 0


// Helpers for dispatching based on number of arguments.  Taken from
// https://stackoverflow.com/a/16683147

#define CAT( A, B ) A ## B
#define SELECT( NAME, NUM ) CAT( NAME ## _, NUM )

#define GET_COUNT( _1, _2, _3, _4, _5, _6 /* ad nauseam */, COUNT, ... ) COUNT
#define VA_SIZE( ... ) GET_COUNT( __VA_ARGS__, 6, 5, 4, 3, 2, 1 )

#define VA_SELECT( NAME, ... ) SELECT( NAME, VA_SIZE(__VA_ARGS__) )(__VA_ARGS__)
