#ifndef __HMAC_SHA_256_H__
#define __HMAC_SHA_256_H__

void hmac_sha256 (const byte *key,size_t key_size,
		  const byte *message,size_t message_size,
		  byte *result);
/*$ spec hmac_sha256(
                     pointer key,
                     size_t key_size,
                     pointer message,
                     size_t message_size,
                     pointer result
                     );
    requires true;
    ensures true;
 $*/
#endif