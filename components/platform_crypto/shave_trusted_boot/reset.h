
#ifndef __RESET_H__
#define __RESET_H__

#define NOT_ALLOWED (-1)
#define HASH_MISMATCH (-2)

typedef unsigned char byte;

#define MEASURE_SIZE (32)

/*$ function (i32) MEASURE_SIZE() $*/
static
int c_MEASURE_SIZE() /*$ cn_function MEASURE_SIZE; $*/ { return MEASURE_SIZE; }

int reset(byte *start_address,
	  byte *end_address,
	  const byte *expected_measure,
	  void *entry);

#endif
