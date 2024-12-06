#ifndef __CN_WARS_H__
#define __CN_WARS_H__
// general things not yet supported by CN

// define that we are using CN for code checking
// NOTE: eventually we don't want to differentiate between the checked
// code and the deployed code
#define CN_ENV 1

// CN issue https://github.com/rems-project/cerberus/issues/254
// Local variables need to be Owned when entering loops
#define WAR_CN_254 1

// CN issue https://github.com/rems-project/cerberus/issues/284
// GCC atributes not supported
#define WAR_CN_284 1
#ifdef WAR_CN_284
#if WAR_CN_284
#define __attribute__(...)
#endif
#endif

// CN issue https://github.com/rems-project/cerberus/issues/285
// Function pointers not supported
#define WAR_CN_285 1

// CN issue https://github.com/rems-project/cerberus/issues/309
// String literals are created in the global context but the function doesn't
// have a resource for them
#define WAR_CN_309

// CN issue https://github.com/rems-project/cerberus/issues/353
// It's not possible to use static local variables
#define WAR_CN_353 1

// CN issue https://github.com/rems-project/cerberus/issues/358
// posix headers exist, but they're only accessible as posix/unistd.h rather
// than unistd.h and they fail when including other posix headers
#define WAR_CN_358

// CN issue https://github.com/GaloisInc/VERSE-Toolchain/issues/103
// memcmp not supported
#define WAR_VERSE_TOOLCHAIN_103 1

// the simplest workaround for unions (making it a struct) don't make sense if
// the union is used to access the same data from different perspectives, but if
// it's just used as a simple sum type it's merely wasteful to use a struct
// instead.
#define WAR_NO_UNIONS 1

// no workaround besides not using it
#define WAR_NO_DOUBLES 1

// no workaround besides not using it
#define WAR_NO_VARIADICS 1

// CN can handle them but working with them in arbitrary orders is currently difficult
#define WAR_NESTED_ARRAYS 1

#if WAR_NO_DOUBLES
#define double unsigned long
#endif

// define out things we can't handle yet
#ifdef WAR_NO_VARIADICS
#define fprintf(a,b,...) fprintf(a,b)
#define fscanf(a,b,...) fscanf(a,b)
#define printf(a,...) printf(a)
#define sprintf(a,b,...) sprintf(a,b)
#define snprintf(a,b,c,...) snprintf(a,b,c)
#define scanf(a,...) scanf(a)
#define sscanf(a,b,...) sscanf(a,b)
#endif

// CN issue https://github.com/rems-project/cerberus/issues/437
// Some headers mention structs only as f(struct x *y) and never define x. C
// accepts this but CN rejects it
#define WAR_CN_437 1

#ifdef WAR_CN_437
// this is required so we can mention FILE* parameters
struct _IO_FILE {
    int x;
};
#endif

#endif // __CN_WARS_H__
