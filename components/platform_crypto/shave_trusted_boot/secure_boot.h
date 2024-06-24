#ifndef __SECURE_BOOT_H__
#define __SECURE_BOOT_H__


#define NOT_ALLOWED (-1)
#define HASH_MISMATCH (-2)
#define MEASURE_SIZE (32)

/*$ function (i32) MEASURE_SIZE() $*/
static
int c_MEASURE_SIZE() /*$ cn_function MEASURE_SIZE; $*/ { return MEASURE_SIZE; }

typedef unsigned char byte;

int read_partition(const char *filename, byte * current_partition, long *file_size);
int read_expected_measurement(const char * filename, byte * expected_measurement);
int reset(byte *start_address,
	  byte *end_address,
	  const byte *expected_measure,
	  void *entry);

#endif // __SECURE_BOOT_H__