#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "secure_boot.h"
#include "sha_256.h"

#ifdef WITH_ATTEST
// must go in special protected storage (writable only by firmware/hardware)
static byte last_measure[MEASURE_SIZE];  // initial contents unimportant
#endif

#if WAR_CN_284
static unsigned int boot_once;
#else
static unsigned int boot_once __attribute__ ((section (".tbootdata") ));
#endif

/*$
predicate {bool b} MyPredicate (pointer expected_measure)
{
  if (is_null(expected_measure)) {
    return {b: false};
  } else {
    take a1 = each(i32 j; 0i32 <= j && j < MEASURE_SIZE()) { Owned<int>(array_shift<byte>(expected_measure,j)) };
    return {b: true};
  }
}
$*/

// NOTE: stack size limit is 8MB on Linux
byte current_partition[1024 * 1024 * 8];

char command[256] = {"whoami"};
char *cmdArgs[] = {NULL};

/**
 * For linux VMs, wrap the binary we want to measure
 * with `execvp()` call to boot into the application.
 * 
 * For embedded code, this should jump straight to `main()`
 */
void entry(void) {
    execvp(command,cmdArgs);
}


/**
 * Reads the content of the file specified by `filename` into the buffer `current_partition`
 * and updates `file_size` with the size of the file.
 *
 * @requires valid_filename: \valid_read(filename);
 *            This ensures that the filename pointer is valid for reading.
 *
 * @requires valid_buffer: \valid(current_partition);
 *            This ensures that the buffer pointer is valid for writing.
 *
 * @requires valid_file_size: \valid(file_size);
 *            This ensures that the file_size pointer is valid for writing.
 *
 * @assigns *current_partition, *file_size;
 *          This specifies that the function may modify the memory pointed to by current_partition and file_size.
 *
 * @ensures file_read_success: \result == 0 ==> \valid_read(current_partition + (0 .. *file_size - 1));
 *           This ensures that if the function returns 0 (success), the buffer has been successfully filled with file_size bytes.
 *
 * @ensures file_read_failure: \result != 0 ==> *file_size == \old(*file_size);
 *           This ensures that if the function does not return 0 (failure), the file_size remains unchanged.
 *
 * @behavior file_exists:
 *           assumes file_exists: \exists char* f; strcmp(filename, f) == 0;
 *           ensures file_size_positive: \result == 0 ==> *file_size > 0;
 *           This describes the behavior when the file exists and can be read, resulting in a positive file size.
 *
 * @behavior file_not_found:
 *           assumes file_not_exists: !(\exists char* f; strcmp(filename, f) == 0);
 *           ensures error_returned: \result != 0;
 *           This describes the behavior when the file does not exist, resulting in an error return value.
 *
 * @complete behaviors;
 * @disjoint behaviors;
 */
int read_partition(const char *filename, byte * current_partition, long *file_size)
{
    FILE *file = fopen(filename, "rb");
    if (file == NULL) {
        fprintf(stderr, "Failed to open file %s\n", filename);
        return -1;
    }

    // Seek to the end of the file to determine its size
    fseek(file, 0, SEEK_END);
    *file_size = ftell(file);
    fseek(file, 0, SEEK_SET); // Seek back to the start of the file

    // Read the file into the binary array
    fread(current_partition, sizeof(unsigned char), *file_size, file);
    fclose(file);

    return 0;
}

/**
 * Open file `filename` and read the expected measurement into `expected_measurement`.
 * The `filename` is expected to contain a 32-byte hash, encoded as 64 hexadecimal characters.
 * Reads 32-byte from the file, converting those characters into a byte array.
 * Returns -1 if the file could not be opened, or if there's an error reading the file.
 * Returns -2 if an invalid hexadecimal character was encountered.
 *
 * @requires valid_filename: \valid_read(filename);
 *            This ensures that the filename pointer is valid for reading.
 *
 * @requires valid_measurement: \valid(expected_measurement + (0 .. 31));
 *            This ensures that the expected_measurement pointer is valid for writing 32 bytes.
 *
 * @assigns *expected_measurement;
 *          This specifies that the function may modify the memory pointed to by expected_measurement.
 *
 * @ensures file_open_failure: \result == -1 ==> \forall int i; 0 <= i < 32 ==> expected_measurement[i] == \old(expected_measurement[i]);
 *           This ensures that if the function returns -1 (file open failure), the expected_measurement array remains unchanged.
 *
 * @ensures invalid_hex_character: \result == -2 ==> \exists int i; 0 <= i < 32 && \valid_read(expected_measurement + i);
 *           This ensures that if the function returns -2 (invalid hexadecimal character), there exists at least one byte in expected_measurement that was attempted to be set.
 *
 * @ensures success: \result == 0 ==> \forall int i; 0 <= i < 32 ==> \valid_read(expected_measurement + i);
 *           This ensures that if the function returns 0 (success), all bytes in expected_measurement are valid and have been set based on the file content.
 *
 * @behavior file_open_error:
 *           assumes file_cannot_open: fopen(filename, "r") == \null;
 *           ensures error_returned: \result == -1;
 *           This describes the behavior when the file cannot be opened, resulting in an error return value.
 *
 * @behavior invalid_hex:
 *           assumes hex_error: \exists int i; 0 <= i < 32 && *endptr != '\0';
 *           ensures error_returned: \result == -2;
 *           This describes the behavior when an invalid hexadecimal character is encountered, resulting in an error return value.
 *
 * @behavior success_read:
 *           assumes valid_file_and_hex: fopen(filename, "r") != \null && \forall int i; 0 <= i < 32 ==> *endptr == '\0';
 *           ensures successful_read: \result == 0;
 *           This describes the behavior when the file is successfully opened and all hexadecimal characters are valid, resulting in a successful read.
 *
 * @complete behaviors;
 * @disjoint behaviors;
 */
int read_expected_measurement(const char * filename, byte * expected_measurement)
{
    FILE *file = fopen(filename, "r");
    if (file == NULL) {
        perror("Failed to open file");
        return -1;
    }
    char hex[3] = {0};
    for (int i = 0; i < 32; i++) {
        if (fread(hex, sizeof(char), 2, file) != 2) {
            fprintf(stderr, "Failed to read character at index %i\n", i);
            fclose(file);
            return -1;
        }
        char *endptr;
        expected_measurement[i] = strtol(hex, &endptr, 16);
        if (*endptr != '\0') {
            fprintf(stderr, "Invalid hexadecimal character in expected measurement\n");
            fclose(file);
            return -2;
        }
    }
    fclose(file);
    return 0;
}


/**
 * Hash the memory region from `start_address` to `end_address` using
 * the SHA256 algorithm. Compare that hash against `expected_measure`.
 * If they are equal and `WITH_ATTEST` is enabled, store the measure
 * into `last_measure`. If they are equal, jump to `entry`.
 *
 * @requires valid_range: \valid_read(start_address + (0 .. end_address - start_address));
 *            This ensures the memory region from start_address to end_address is valid for reading.
 *
 * @requires valid_measure: expected_measure == NULL || \valid_read(expected_measure + (0 .. MEASURE_SIZE-1));
 *            This ensures expected_measure is either NULL or points to a valid readable block of memory of MEASURE_SIZE.
 *
 * @requires valid_entry: entry != \null;
 *            This ensures that the entry pointer is valid and not null.
 *
 * @assigns last_measure[0 .. MEASURE_SIZE-1];
 *          This specifies that last_measure may be modified by the function.
 *
 * @ensures measure_equality: \result == 0 ==> (\forall integer i; 0 <= i < MEASURE_SIZE ==> \old(last_measure[i]) == last_measure[i]);
 *           This ensures that if the function returns 0, the last_measure array remains unchanged unless WITH_ATTEST is defined and the measures are equal.
 *
 * @behavior measure_match:
 *           assumes measure_valid: expected_measure != NULL && \valid_read(expected_measure + (0 .. MEASURE_SIZE-1));
 *           assumes measure_equal: HashEquals(start_address, end_address, expected_measure) == 1;
 *           ensures jump_to_entry: \result == 0;
 *           This describes the behavior when the expected_measure is valid, not NULL, and matches the computed hash.
 *
 * @behavior measure_mismatch:
 *           assumes measure_valid: expected_measure != NULL && \valid_read(expected_measure + (0 .. MEASURE_SIZE-1));
 *           assumes measure_not_equal: HashEquals(start_address, end_address, expected_measure) == 0;
 *           ensures no_jump: \result == -1;
 *           This describes the behavior when the expected_measure is valid, not NULL, but does not match the computed hash.
 *
 * @complete behaviors;
 * @disjoint behaviors;
 */
int reset(byte *start_address,
          byte *end_address,
          const byte *expected_measure,
          void *entry)
/*$
  requires take b1 = Owned<unsigned int>(&boot_once);
  requires take x = MyPredicate(expected_measure);
  //requires is_null(expected_measure) == true;
  //requires take x =  Owned<byte>(expected_measure);
  ensures take b2 = Owned<unsigned int>(&boot_once);
  //ensures take x1 =  Owned<byte>(expected_measure);
  //ensures is_null(expected_measure);
  ensures take y = MyPredicate(expected_measure);
$*/
{
  // Frama-C doesn't like reasoning about a local variable
#ifndef WITH_ATTEST
  byte last_measure[MEASURE_SIZE];  
#endif


  if (boot_once) {
    return NOT_ALLOWED;
  }

  // compute region size (possibly 0)
  size_t region_size = (end_address < start_address) ? 0 : ((size_t) end_address - (size_t) start_address);
  printf("region_size: %ld\n", region_size);

  // apply SHA-256 to region 
  SHA256((byte *)start_address,region_size,&last_measure[0]);

#ifdef DEBUG_PRINT
  // iteratively print characters in last_measure and expected_measure
  printf("last_measure: ");
  for (int i = 0; i < MEASURE_SIZE; i++) {
    printf("%02x ", last_measure[i]);
  }
  printf("\n");

  printf("expected_measure: ");
  if (expected_measure != NULL) {
    for (int i = 0; i < MEASURE_SIZE; i++) {
      printf("%02x ", expected_measure[i]);
    }
  }
  printf("\n");
#endif // DEBUG_PRINT

  // compare measure to expected measure (if it was provided)
  if ((expected_measure != NULL)
#if !WAR_VERSE_TOOLCHAIN_103
      &&
      (memcmp(last_measure,expected_measure,MEASURE_SIZE) != 0))
#else
    )
#endif
    return HASH_MISMATCH;

  boot_once = 1;

  // CLEAR STATE
  // zero memory outside of region, registers, any other visible state
  // (may require assembler)

#if !WAR_CN_285
  printf("Jumping to entry\n");
  void (*f)() = entry;
  f();
#endif

  // should never reach here
  return 0;
}

#ifdef WITH_ATTEST

#include "hmac_sha256.h"
#define KEY_SIZE (32)
#define NONCE_SIZE (16)
#define HMAC_SIZE (32)
  
// must go in special protected storage (read-only, readable only by firmware/hardware)
static byte key[KEY_SIZE]; // how does this get initialized?

/**
 * Perform attestation---checking that a system was booted from a
 * known state in the past---on a system that has been booted with
 * trusted boot. A provisioned key is used to check the attestation
 * and a nonce is provided as part of the attestation protocol. They
 * key is typically provisioned into a specially protected store or is
 * automatically generated by the hardware during fabrication and
 * first initialization. The nonce is typically provided interactively
 * by attestation hardware or a remote protocol.
 *
 * This function only exists if `WITH_ATTEST` is enabled, and can be
 * called after a call to `reset()` has been successfully called, and
 * thus the system's initial state has been measured and the trusted
 * boot process has saved that validated measure in `last_measure`.
 *
 * Because `reset()` does not return, to use attestation we would need
 * an additional boot stage, which handles attestation and then jumps
 * to the application. This is not implemented here.
 *
 * If `hmac` is non-NULL, perform an HMAC-SHA256 on the catenation of
 * `last_measure` and `nonce` using an externally provisioned and
 * protected `key`.  If `measure` is non-NULL write that HMAC value to
 * `measure`.
 */
// /*@ requires hmac == NULL || \valid_read(nonce + (0 .. NONCE_SIZE-1));
//     requires measure == NULL || \valid(measure + (0 .. MEASURE_SIZE-1));
//     requires hmac == NULL || \valid(hmac + (0 .. HMAC_SIZE-1));
//     assigns measure[0 .. MEASURE_SIZE-1] \from last_measure[0 .. MEASURE_SIZE-1];
//     assigns hmac[0 .. HMAC_SIZE-1] \from last_measure[0 .. MEASURE_SIZE-1], nonce[0 .. NONCE_SIZE-1], key[0 .. KEY_SIZE-1];
//     requires measure == NULL || \separated(measure + (0 .. MEASURE_SIZE-1),last_measure + (0 .. MEASURE_SIZE-1));
//     requires hmac == NULL || \separated(hmac + (0 .. HMAC_SIZE-1),last_measure + (0 .. MEASURE_SIZE-1));
//     requires measure == NULL || \separated(measure + (0 .. MEASURE_SIZE-1),key + (0 .. KEY_SIZE-1));
//     requires hmac == NULL || \separated(hmac + (0 .. HMAC_SIZE-1),key + (0 .. KEY_SIZE-1));
// @*/
/**
 * Performs an HMAC-SHA256 operation on the concatenation of `last_measure` and `nonce`
 * using an externally provisioned and protected `key`, if `hmac` is non-NULL.
 * If `measure` is non-NULL, writes the HMAC value to `measure`.
 *
 * @requires valid_nonce: hmac == NULL || \valid_read(nonce + (0 .. NONCE_SIZE-1));
 *            This ensures that if `hmac` is not NULL, `nonce` must point to a valid memory location of size `NONCE_SIZE`.
 *
 * @requires valid_measure: measure == NULL || \valid(measure + (0 .. MEASURE_SIZE-1));
 *            This ensures that if `measure` is not NULL, it must point to a valid memory location of size `MEASURE_SIZE`.
 *
 * @requires valid_hmac: hmac == NULL || \valid(hmac + (0 .. HMAC_SIZE-1));
 *            This ensures that if `hmac` is not NULL, it must point to a valid memory location of size `HMAC_SIZE`.
 *
 * @assigns measure[0 .. MEASURE_SIZE-1] \from last_measure[0 .. MEASURE_SIZE-1];
 *          Specifies that `measure` may be modified based on the contents of `last_measure`.
 *
 * @assigns hmac[0 .. HMAC_SIZE-1] \from last_measure[0 .. MEASURE_SIZE-1], nonce[0 .. NONCE_SIZE-1], key[0 .. KEY_SIZE-1];
 *          Specifies that `hmac` may be modified based on the contents of `last_measure`, `nonce`, and `key`.
 *
 * @requires separated_measure_last_measure: measure == NULL || \separated(measure + (0 .. MEASURE_SIZE-1),last_measure + (0 .. MEASURE_SIZE-1));
 *            Ensures that `measure` and `last_measure` do not overlap if `measure` is not NULL.
 *
 * @requires separated_hmac_last_measure: hmac == NULL || \separated(hmac + (0 .. HMAC_SIZE-1),last_measure + (0 .. MEASURE_SIZE-1));
 *            Ensures that `hmac` and `last_measure` do not overlap if `hmac` is not NULL.
 *
 * @requires separated_measure_key: measure == NULL || \separated(measure + (0 .. MEASURE_SIZE-1),key + (0 .. KEY_SIZE-1));
 *            Ensures that `measure` and `key` do not overlap if `measure` is not NULL.
 *
 * @requires separated_hmac_key: hmac == NULL || \separated(hmac + (0 .. HMAC_SIZE-1),key + (0 .. KEY_SIZE-1));
 *            Ensures that `hmac` and `key` do not overlap if `hmac` is not NULL.
 */
void attest(const byte *nonce,  // Ignored if hmac == NULL
	    byte *measure,  // IF NULL, do not return measure
	    byte *hmac)  // If NULL, do not return hmac
{

  if (hmac != NULL) {
    // prepare hmac text
    byte hmac_text[MEASURE_SIZE+NONCE_SIZE];
#if !WAR_VERSE_TOOLCHAIN_103
    memcpy(&hmac_text[0],last_measure,MEASURE_SIZE);
    memcpy(&hmac_text[MEASURE_SIZE],nonce,NONCE_SIZE);
#endif

    //do hmac to target buffer
    hmac_sha256(key,KEY_SIZE,hmac_text,MEASURE_SIZE+NONCE_SIZE,hmac);
  }

  if (measure != NULL) {
    //copy out measure to target buffer
#if !WAR_VERSE_TOOLCHAIN_103
    memcpy(measure,last_measure,MEASURE_SIZE);
#endif
  }
}

#endif // WITH_ATTEST

/**
 * The entry for the OpenSUT secure boot
 * 
 * This code will:
 * - read the application binary (or elf.file)
 * - read a file with stored measure
 * - pass the appropriate values to reset()
 * - if the measures match, jump to the application (the elf file specified)
 */
int main(int argc, char *argv[])
{
    if (argc < 2) {
        printf("Usage: %s <filename>\n", argv[0]);
        return 1;
    }

    const char *filename = argv[1];
    long file_size = 0;

    if (read_partition(filename, current_partition, &file_size) != 0) {
        fprintf(stderr, "Failed to read partition!\n");
        return -1;
    }

    byte expected_measurement[MEASURE_SIZE] = {0};
    if (argc >= 3) {
        printf("Reading expected measurement from file %s\n", argv[2]);
        if (read_expected_measurement(argv[2], expected_measurement) != 0) {
            fprintf(stderr, "Failed to read expected measurement!\n");
            return -1;
        }
    }

    // Prepare the command to be executed
    strcpy(command, filename);

    // Actual call to the secure boot
    printf("file_size: %ld\n", file_size);
    // Note it is legal to point "one past the end of the array" in C, hence passing &current_partition[file_size]
    switch (reset(&current_partition[0], &current_partition[file_size], (argc >= 3) ? expected_measurement : NULL, &entry)) {
        case NOT_ALLOWED:
            printf("Reset not allowed\n");
            break;
        case HASH_MISMATCH:
            printf("Hash mismatch\n");
            break;
        default:
            break;
    }

    printf("Ending-----\n");
    return 0;
}