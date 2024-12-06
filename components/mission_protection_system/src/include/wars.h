// general things not yet supported by CN

// define that we are using CN for code checking
// NOTE: eventually we don't want to differentiate between the checked
// code and the deployed code
#define CN_ENV 1

// the simplest workaround for unions (making it a struct) don't make sense if
// the union is used to access the same data from different perspectives, but if
// it's just used as a simple sum type it's merely wasteful to use a struct
// instead.
#define WAR_NO_UNIONS 1

// no workaround besides not using it
#define WAR_NO_DOUBLES 1

// no workaround besides not using it
#define WAR_NO_VARIADICS 1

// CN issue #233, left shift on unsigned char and short crashes. Cast to a
// larger or signed type then back.
#define WAR_CN_233 1

// CN issue  #231, crash on / or %
#define WAR_CN_231 1

#if WAR_NO_DOUBLES
#define double unsigned long
#endif

// We are compiling for the POSIX target
#define PLATFORM_HOST
