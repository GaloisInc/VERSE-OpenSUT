// general things not yet supported by CN

// define that we are using CN for code checking
// NOTE: eventually we don't want to differentiate between the checked
// code and the deployed code
#define CN_ENV 1

// CN issue https://github.com/rems-project/cerberus/issues/284
// GCC atributes not supported
#define WAR_CN_284 1

// CN issue https://github.com/rems-project/cerberus/issues/285
// Function pointers not supported
#define WAR_CN_285 1

// CN issue https://github.com/GaloisInc/VERSE-Toolchain/issues/103
// memcmp not supported
#define WAR_VERSE_TOOLCHAIN_103 1