
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

#endif
