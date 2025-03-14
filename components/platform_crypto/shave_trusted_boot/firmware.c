// @todo check that code makes sense under both 32 and 64 bit models

// Two versions incorporated here based on definition WITH_ATTEST

#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include <stdbool.h>

#include "sha_256.h"
#include "hmac_sha256.h"
#include "reset.h"
#ifdef CN_ENV
#include "cn_memory.h"
#include "cn_array_utils.h"
#define memcpy(f,b,s) _memcpy(f,b,s)
#define memcmp(f,b,s) _memcmp(f,b,s)
#define malloc(x) _malloc(x)
#define free _free
#define realloc _realloc
#endif

//#define _Static_assert(...) extern int bogus
#if defined(USE_XMSS)
#define union struct
#define __STDC_NO_ATOMICS__ 1
#include "endianness.h"
#include "signing.h"
#include "signing_private.h"
#include "verification.h"
#endif


#if defined(USE_XMSS)
static bool xmss_verify_signature(XmssPublicKey *exported_public_key, uint8_t *msg, size_t msg_size, XmssSignatureBlob *signature_blob)
/*$
  requires
    take epki = Owned<XmssPublicKey>(exported_public_key);
    take mi = ArrayOwned_u8(msg, msg_size);
    take sbi = XmssSignatureBlobP(signature_blob);

  ensures
    take epko = Owned<XmssPublicKey>(exported_public_key);
    take mo = ArrayOwned_u8(msg, msg_size);
    take sbo = XmssSignatureBlobP(signature_blob);
    sbi.data_size == sbo.data_size;
$*/
{
    bool success = true;

    XmssBuffer message = {msg_size, msg};

    XmssVerificationContext verification_ctx = {0};
    XmssSignature *signature = NULL;

    const uint8_t *volatile part_verify = NULL;

    // Verify that the signature verifies
    signature = xmss_get_signature_struct(signature_blob);
    success = success && XMSS_OKAY == xmss_verification_init(&verification_ctx, exported_public_key, signature,
        signature_blob->data_size);
    success = success && XMSS_OKAY == xmss_verification_update(&verification_ctx, message.data, message.data_size,
        &part_verify);
    success = success && part_verify == message.data;
    success = success && XMSS_OKAY == xmss_verification_check(&verification_ctx, exported_public_key);
    // redundant, for fault tolerance
    success = success && XMSS_OKAY == xmss_verification_check(&verification_ctx, exported_public_key);

    /*$ apply Unxmss_get_signature_struct(signature_blob, signature); $*/

    return success;
}
#endif

typedef unsigned char byte;

#ifdef USE_XMSS
#define MEASURE_SIZE (XMSS_SIGNATURE_BLOB_SIZE(XMSS_PARAM_SHA2_10_256)-sizeof(size_t))
#else
#define MEASURE_SIZE (32)
#endif
/*$ function (u64) MEASURE_SIZE() $*/
static
uint64_t c_MEASURE_SIZE() /*$ cn_function MEASURE_SIZE; $*/ { return MEASURE_SIZE; }

#if defined(WITH_ATTEST) || defined(CN_ENV)
// must go in special protected storage (writable only by firmware/hardware)
static byte last_measure[MEASURE_SIZE];  // initial contents unimportant
#if defined(USE_XMSS)
static XmssPublicKey public_key;
#else
static bool public_key;
#endif
#endif

static unsigned int boot_once __attribute__ ((section (".tbootdata") ));

static void magically_call(void (*f)(void))
/*$ trusted; $*/
{
  f();
}
/**
 * Hash the memory region from `start_address` to `end_address` using
 * the SHA256 algorithm. Compare that hash against `expected_measure`.
 * If they are equal and `WITH_ATTEST` is enabled, store the measure
 * into `last_measure`. If they are equal, jump to `entry`.
 *
 * Implements:  TA2-REQ-57
 *
 * Implements:  TA2-REQ-54, TA2-REQ-55
 */
/*@ requires expected_measure == NULL || \valid_read(expected_measure + (0 .. MEASURE_SIZE-1));
    assigns last_measure[0 .. MEASURE_SIZE-1];
    // \valid clause on (start_address .. end_address)

 */
int reset(void *start_address,
	  void *end_address,
	  const void *expected_measure,  // If NULL, skip the measurement test and always transfer control to entry
                                         // Note: it is harmless for this buffer to be within measured region
	  void *entry)
  // TODO need a trick for start and end address. In particular note than this range can contain expected_measure
/*$ accesses boot_once;
  accesses last_measure;
  accesses public_key;
  requires
    take si = each(u64 i; i >= 0u64 && i < (((u64)end_address) - ((u64)start_address))) { Owned<uint8_t>(array_shift<uint8_t>(start_address, i))};
    take emi = ArrayOrNull_u8(expected_measure, MEASURE_SIZE());
  ensures
    take so = each(u64 i; i >= 0u64 && i < (((u64)end_address) - ((u64)start_address))) { Owned<uint8_t>(array_shift<uint8_t>(start_address, i))};
    take emo = ArrayOrNull_u8(expected_measure, MEASURE_SIZE());
    emi==emo;
$*/
{
#if !defined(WITH_ATTEST) && !defined(CN_ENV)
  byte last_measure[MEASURE_SIZE];
#endif


  unsigned char *expected_measure_ = (unsigned char *) expected_measure;
  if (boot_once) {
    return NOT_ALLOWED;
  }

  // compute region size (possibly 0)
  // @todo: is this a legal way to do the pointer subtraction in C?
  uintptr_t e = (uintptr_t)end_address;
  uintptr_t s = (uintptr_t)start_address;
#ifndef CN_ENV
  // CN doesn't allow this comparison because these are not pointers within the
  // same object. This is entirely correct, these are pointers into memory
  // filled by the linker. We need a good way to handle such regions.
  size_t region_size = (end_address < start_address) ? 0 : (e - s);
#else
  size_t region_size = (e < s) ? 0 : (e - s);
#endif

// Implements:  TA2-REQ-59, TA2-REQ-60
#if defined(USE_XMSS)
  if (expected_measure == NULL) {
      return NOT_ALLOWED;
  }

  _Static_assert(XMSS_SIGNATURE_BLOB_SIZE(XMSS_PARAM_SHA2_10_256) == (MEASURE_SIZE+sizeof(size_t)), "MEASURE_SIZE is big enough");
  size_t blob_size = XMSS_SIGNATURE_BLOB_SIZE(XMSS_PARAM_SHA2_10_256);
  XmssSignatureBlob *sig = malloc(blob_size);
  if (!sig) {
      return NOT_ALLOWED;
  }

  void *sig_data_ = &sig->data;
  /*$ apply SplitAt_Block_u8(sig, blob_size, 0u64, sizeof<size_t>); $*/
  /*$ apply ViewShift_Block_u8(sig, sig_data_, sizeof<size_t>, blob_size-sizeof<size_t>); $*/
  /*$ from_bytes Block<size_t>(member_shift<XmssSignatureBlob>(sig, data_size)); $*/
  sig->data_size = MEASURE_SIZE;
  memcpy(sig_data_, expected_measure_, MEASURE_SIZE);
  if (!xmss_verify_signature(&public_key, start_address, region_size, sig)) {
      /*$ to_bytes Block<size_t>(member_shift<XmssSignatureBlob>(sig, data_size)); $*/
      /*$ apply UnViewShift_Owned_u8(sig, sig_data_, sizeof<size_t>, blob_size-sizeof<size_t>); $*/
      /*$ apply UnSplitAt_Block_u8(sig, blob_size, 0u64, sizeof<size_t>); $*/
      free(sig);
      return HASH_MISMATCH;
  }
  /*$ to_bytes Block<size_t>(member_shift<XmssSignatureBlob>(sig, data_size)); $*/
  /*$ apply UnViewShift_Block_u8(sig, sig_data_, sizeof<size_t>, blob_size-sizeof<size_t>); $*/
  /*$ apply UnSplitAt_Block_u8(sig, blob_size, 0u64, sizeof<size_t>); $*/
  free(sig);
#else
  // apply SHA-256 to region
  SHA256((byte *)start_address,region_size,&last_measure[0]);
  // Implements:  TA2-REQ-62, TA2-REQ-64
  // compare measure to expected measure (if it was provided)
  if ((expected_measure_ != NULL)
      &&
      (memcmp(last_measure,expected_measure_,MEASURE_SIZE) != 0))
    return HASH_MISMATCH;
#endif

  boot_once = 1;

  // CLEAR STATE
  // zero memory outside of region, registers, any other visible state
  // (may require assembler)

  void (*f)(void) = (void (*)(void))entry;
#ifndef CN_ENV
  f();
#else
  magically_call(f);
#endif

  // should never reach here
  return 0;
}

#ifdef WITH_ATTEST

#define KEY_SIZE (32)
/*$ function (u64) KEY_SIZE() $*/
static
uint64_t c_KEY_SIZE() /*$ cn_function KEY_SIZE; $*/ { return KEY_SIZE; }
#define NONCE_SIZE (16)
/*$ function (u64) NONCE_SIZE() $*/
static
uint64_t c_NONCE_SIZE() /*$ cn_function NONCE_SIZE; $*/ { return NONCE_SIZE; }
#define HMAC_SIZE (32)
/*$ function (u64) HMAC_SIZE() $*/
static
uint64_t c_HMAC_SIZE() /*$ cn_function HMAC_SIZE; $*/ { return HMAC_SIZE; }

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
 * If `hmac` is non-NULL, perform an HMAC-SHA256 on the catenation of
 * `last_measure` and `nonce` using an externally provisioned and
 * protected `key`.  If `measure` is non-NULL write that HMAC value to
 * `measure`.
 *
 * Implements: TA2-REQ-65
 */
/*@ requires hmac == NULL || \valid_read(nonce + (0 .. NONCE_SIZE-1));
    requires measure == NULL || \valid(measure + (0 .. MEASURE_SIZE-1))
    requires hmac == NULL || \valid(hmac + (0 .. HMAC_SIZE-1));
    assigns measure[0 .. MEASURE_SIZE-1] \from last_measure[0 .. MEASURE_SIZE-1];
    assigns hmac[0 .. HMAC_SIZE-1] \from last_measure[0 .. MEASURE_SIZE-1], nonce[0 .. NONCE_SIZE-1], key[0 .. KEY_SIZE-1];
    requires measure == NULL || \separated(measure + (0 .. MEASURE_SIZE-1),last_measure + (0 .. MEASURE_SIZE-1));
    requires hmac == NULL || \separated(hmac + (0 .. HMAC_SIZE-1),last_measure + (0 .. MEASURE_SIZE-1));
    requires measure == NULL || \separated(measure + (0 .. MEASURE_SIZE-1),key + (0 .. KEY_SIZE-1));
    requires hmac == NULL || \separated(hmac + (0 .. HMAC_SIZE-1),key + (0 .. KEY_SIZE-1));
*/
void attest(const byte *nonce,  // Ignored if hmac == NULL
	    byte *measure,  // IF NULL, do not return measure
	    byte *hmac)  // If NULL, do not return hmac
/*$
  accesses last_measure;
  accesses key;
  requires
    take ni = CondArraySliceOwned_u8(nonce, !is_null(hmac), 0u64, NONCE_SIZE());
    take mi = ArrayOrNull_u8(measure, MEASURE_SIZE());
    take hi = ArrayOrNull_u8(hmac, HMAC_SIZE());
  ensures
    take no = CondArraySliceOwned_u8(nonce, !is_null(hmac), 0u64, NONCE_SIZE());
    take mo = ArrayOrNull_u8(measure, MEASURE_SIZE());
    take ho = ArrayOrNull_u8(hmac, HMAC_SIZE());
    ni == no;
$*/
{

  if (hmac != NULL) {
    // prepare hmac text
    byte hmac_text[MEASURE_SIZE+NONCE_SIZE];
    // These are present because CN doesn't allow us to use the array directly in
    // lemma arguments, or '&' at all
    byte *hmac_text_0 = hmac_text;
    byte *hmac_text_MEASURE_SIZE = &hmac_text[MEASURE_SIZE];

    /*$ apply SplitAt_Block_u8(hmac_text_0, MEASURE_SIZE()+NONCE_SIZE(), MEASURE_SIZE(), NONCE_SIZE()); $*/
    memcpy((unsigned char*)&hmac_text[0],last_measure,MEASURE_SIZE);

    /*$ apply ViewShift_Block_u8(hmac_text_0, hmac_text_MEASURE_SIZE, MEASURE_SIZE(), NONCE_SIZE()); $*/
    memcpy((unsigned char*)&hmac_text[MEASURE_SIZE],(unsigned char*)nonce,NONCE_SIZE);
    /*$ apply UnViewShift_Owned_u8(hmac_text_0, hmac_text_MEASURE_SIZE, MEASURE_SIZE(), NONCE_SIZE()); $*/
    /*$ apply UnSplitAt_Owned_u8(hmac_text_0, MEASURE_SIZE()+NONCE_SIZE(), MEASURE_SIZE(), NONCE_SIZE()); $*/

    //do hmac to target buffer
    hmac_sha256(key,KEY_SIZE,hmac_text,MEASURE_SIZE+NONCE_SIZE,hmac);
  }

  if (measure != NULL) {
    //copy out measure to target buffer
    memcpy(measure,last_measure,MEASURE_SIZE);
  }
}

#endif
