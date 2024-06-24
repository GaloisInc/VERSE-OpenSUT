#include <stddef.h>
#include <string.h>
#include <assert.h>

typedef unsigned char byte;

extern void SHA256(const byte *d, size_t n, byte *md);

#define BLOCK_SIZE 64
#define DIGEST_SIZE 32

/* // to try and make saw happy */
/* void *memcpy(void *dst, const void *src, size_t n) { */
/*   for (size_t i = 0; i < n; i++) */
/*     *((byte *)dst + i) = *((byte *)src + i); */
/*   return dst; */
/* } */


// This assumes only a top-level full-buffer interface to SHA256.
// It is thus terribly inefficient unless message_size is
// not too much bigger than BLOCK_SIZE (as is the case in our application).
#define MAX_MESSAGE_SIZE 2*BLOCK_SIZE
static byte inner[BLOCK_SIZE+MAX_MESSAGE_SIZE];

void hmac_sha256 (const byte *key,size_t key_size,
		  const byte *message,size_t message_size,
		  byte *result) {
  assert (message_size <= MAX_MESSAGE_SIZE);
  byte key1[BLOCK_SIZE];
  size_t key1_size;
  // hash key if necessary
  if (key_size > BLOCK_SIZE) {
    SHA256(key,key_size,key1);
    key1_size = DIGEST_SIZE;
  } else {
    memcpy(key1,key,key_size);
    key1_size = key_size;
  }
  // zero-pad key if necessary
  for (int i = key1_size; i < BLOCK_SIZE; i++)
    key1[i] = 0;
  // key1 size is now exactly BLOCK_SIZE
  // build inner message
  for (int i = 0; i < BLOCK_SIZE; i++) 
    inner[i] = ((byte) 0x36) ^ key1[i];
  memcpy(&inner[BLOCK_SIZE],message,message_size);
  // build outer message
  byte outer[BLOCK_SIZE+DIGEST_SIZE];
  for (int i = 0; i < BLOCK_SIZE; i++)
    outer[i] = ((byte) 0x5c) ^ key1[i];
  SHA256(inner,BLOCK_SIZE+message_size,&outer[BLOCK_SIZE]);
  SHA256(outer,BLOCK_SIZE+DIGEST_SIZE,result);
}  

// // for testing
// #include <stdio.h>
// int main () {
//   byte key[] = "Jefe";
//   byte message[] = "what do ya want for nothing?";
//   byte result[DIGEST_SIZE];
//   hmac_sha256(key,strlen((char *)key),message,strlen((char *)message),result);
//   for (int i = 0; i < DIGEST_SIZE; i++)
//     printf ("%.2x",result[i]);
//   printf ("\n");
//   // 0x5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843
//   }
