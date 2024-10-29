#ifndef __SHA_256_H__
#define __SHA_256_H__

#include <stddef.h>

/* excerpts from sha.h ------------------------------------------------*/

#define SHA_LONG unsigned int

#define SHA_LBLOCK	16
#define SHA_CBLOCK	(SHA_LBLOCK*4)	/* SHA treats input data as a
					 * contiguous array of 32 bit
					 * wide big-endian values. */

#define SHA256_DIGEST_LENGTH	32
/*$ function (u64) SHA256_DIGEST_LENGTH() $*/
static
unsigned long c_SHA256_DIGEST_LENGTH() /*$ cn_function SHA256_DIGEST_LENGTH; $*/ { return SHA256_DIGEST_LENGTH; }

typedef struct SHA256state_st
	{
	SHA_LONG h[8];
	SHA_LONG Nl,Nh;
	unsigned char data[SHA_CBLOCK];
	unsigned int num;
	} SHA256_CTX;

/* end sha.h ---------------------------------------*/

void SHA256_Init (SHA256_CTX *c);
void SHA256_Update (SHA256_CTX *c, const void *data_, size_t len);
void SHA256_Final (unsigned char *md, SHA256_CTX *c);

void SHA256(const unsigned char *d, size_t n, unsigned char *md);
/*$ spec SHA256(pointer d, u64 n, pointer md);
  requires
    take di = each(u64 j; j >= 0u64 && j < (u64)n) {Owned<unsigned char>(array_shift<unsigned char>(d, j))};
    take mdi = each(u64 j; j >= 0u64 && j < 32u64) {Block<unsigned char>(array_shift<unsigned char>(md, j))};
  ensures
    take d_ = each(u64 j; j >= 0u64 && j < (u64)n) {Owned<unsigned char>(array_shift<unsigned char>(d, j))};
    take mdo = each(u64 j; j >= 0u64 && j < 32u64) {Owned<unsigned char>(array_shift<unsigned char>(md, j))};
    di == d_;
  $*/

#endif
