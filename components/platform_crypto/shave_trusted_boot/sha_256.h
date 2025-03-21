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
/*$ spec SHA256_Init(pointer c);
  // @PropertyClass: P3-SOP
  requires take ci = Block<SHA256_CTX>(c);
  ensures take co = Owned<SHA256_CTX>(c);
$*/
void SHA256_Update (SHA256_CTX *c, const void *data_, size_t len);
/*$ spec SHA256_Update(pointer c, pointer data_, u64 len);
  // @PropertyClass: P3-SOP
  requires take ci = Owned<SHA256_CTX>(c);
    take di = each(u64 i; i >= 0u64 && i < len) {Owned<uint8_t>(array_shift<uint8_t>(data_,i))};
  ensures take co = Owned<SHA256_CTX>(c);
    take d_ = each(u64 i; i >= 0u64 && i < len) {Owned<uint8_t>(array_shift<uint8_t>(data_,i))};
    di == d_;
$*/
void SHA256_Final (unsigned char *md, SHA256_CTX *c);
/*$ spec SHA256_Final(pointer md, pointer c);
  // @PropertyClass: P3-SOP
  requires take ci = Owned<SHA256_CTX>(c);
    take mdi = each(u64 i; i >= 0u64 && i < SHA256_DIGEST_LENGTH()) {Owned<uint8_t>(array_shift<uint8_t>(md,i))};
  ensures take co = Owned<SHA256_CTX>(c);
    take mdo = each(u64 i; i >= 0u64 && i < SHA256_DIGEST_LENGTH()) {Owned<uint8_t>(array_shift<uint8_t>(md,i))};
    mdi == mdo;
$*/

void SHA256(const unsigned char *d, size_t n, unsigned char *md);
/*$ spec SHA256(pointer d, u64 n, pointer md);
  // @PropertyClass: P3-SOP
  requires
    take di = each(u64 j; j >= 0u64 && j < (u64)n) {Owned<unsigned char>(array_shift<unsigned char>(d, j))};
    take mdi = each(u64 j; j >= 0u64 && j < 32u64) {Block<unsigned char>(array_shift<unsigned char>(md, j))};
  ensures
    take d_ = each(u64 j; j >= 0u64 && j < (u64)n) {Owned<unsigned char>(array_shift<unsigned char>(d, j))};
    take mdo = each(u64 j; j >= 0u64 && j < 32u64) {Owned<unsigned char>(array_shift<unsigned char>(md, j))};
    di == d_;
  $*/

#endif
