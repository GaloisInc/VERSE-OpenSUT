
#ifndef __SHA_256_H__
#define __SHA_256_H__

void SHA256(const unsigned char *d, size_t n, unsigned char *md);
/*$ spec SHA256(pointer d, size_t n, pointer md);
    requires true;
    ensures true;
 $*/

#endif
