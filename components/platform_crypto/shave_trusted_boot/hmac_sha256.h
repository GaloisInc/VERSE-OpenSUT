
#ifndef __HMAC_SHA256_H__
#define __HMAC_SHA256_H__

void hmac_sha256 (const unsigned char *key,size_t key_size,
		  const unsigned char *message,size_t message_size,
		  unsigned char *result);

#endif
