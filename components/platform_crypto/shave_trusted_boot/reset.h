
#ifndef __RESET_H__
#define __RESET_H__

#define NOT_ALLOWED (-1)
#define HASH_MISMATCH (-2)

typedef unsigned char byte;

int reset(void *start_address,
	  void *end_address,
	  const byte *expected_measure,
	  void *entry);

#endif
