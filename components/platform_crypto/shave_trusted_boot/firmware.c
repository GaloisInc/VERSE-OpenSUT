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
#define free _free
#define realloc _realloc
#endif

//#define _Static_assert(...) extern int bogus
#if !defined(NO_XMSS)
#define union struct
#define __STDC_NO_ATOMICS__ 1
#include "endianness.h"
#include "signing.h"
#include "signing_private.h"
#include "verification.h"
#endif


#if 0
/*
 * Run sign and verify test, in which a single signature is generated and verified as a sanity check.
 * Generates a key for the provided parameter set, places a signature and verifies that the signature verifies.
*/
static bool sign_verify_test(XmssParameterSetOID test_parameter_set)
{
    bool success = true;

    XmssSigningContext *context_ptr_dynamic = NULL;
    XmssKeyContext *key_context = NULL;
    XmssPrivateKeyStatelessBlob *stateless_blob = NULL;
    XmssPrivateKeyStatefulBlob *stateful_blob = NULL;
    XmssKeyGenerationContext *keygen_context = NULL;
    XmssPublicKeyInternalBlob *public_key_blob = NULL;
    XmssInternalCache *internal_cache = NULL;
    XmssInternalCache *generation_cache = NULL;
    XmssPublicKey exported_public_key = { 0 };
    XmssSignatureBlob *signature_blob = NULL;

    success = success && XMSS_OKAY == xmss_context_initialize(&context_ptr_dynamic, test_parameter_set, realloc, free, NULL);

    uint8_t random[32] = {0};
    uint8_t secure_random[96] = {0};

    XmssBuffer random_buffer = {sizeof(random), random};
    XmssBuffer secure_random_buffer = {sizeof(secure_random), secure_random};
    XmssIndexObfuscationSetting index_obfuscation_setting = XMSS_INDEX_OBFUSCATION_OFF;

    uint8_t message_buffer[1 * 136] = {0};
    XmssBuffer message = {sizeof(message_buffer), message_buffer};

    XmssVerificationContext verification_ctx = {0};
    XmssSignature *signature = NULL;

    const uint8_t *volatile part_verify = NULL;

    /*$ assert(is_null(signature_blob)); $*/
    #if 0
    for (size_t i = 0; i < sizeof(secure_random); i++)
    /*$ inv
      i <= sizeof<uint8_t[96]>;
      take cpdi = Owned<XmssSigningContext>(context_ptr_dynamic);
    $*/
    {
        /*$ extract Owned<uint8_t>, (u64) i; $*/
        secure_random[i] = (uint8_t)i;
    }
    #endif
    /*$ assert(is_null(signature_blob)); $*/

    /* Call xmss_generate_private_key with some reasonable params. */
    success = success && xmss_generate_private_key(&key_context, &stateless_blob, &stateful_blob,
            &secure_random_buffer, index_obfuscation_setting, &random_buffer, context_ptr_dynamic) == XMSS_OKAY;

    success = success && XMSS_OKAY == xmss_generate_public_key(&keygen_context, &internal_cache, &generation_cache,
            key_context, XMSS_CACHE_TOP, 0, 1);
    /*$ assert(success != 0u8); $*/
    success = success && XMSS_OKAY == xmss_calculate_public_key_part(keygen_context, 0);
    success = success && XMSS_OKAY == xmss_finish_calculate_public_key(&public_key_blob, &keygen_context,
            key_context);
    success = success && (keygen_context == NULL);

    success = success && XMSS_OKAY == xmss_export_public_key(&exported_public_key, key_context);
    success = success && XMSS_OKAY == xmss_request_future_signatures(&stateful_blob, key_context, 1);

    /*$ assert(is_null(signature_blob)); $*/
    // The message, 10 * the maximum block size (136 for SHAKE)
    #if 0
    uint8_t message_buffer[10 * 136];
    #endif
    #if 0
    for (size_t i = 0; i < sizeof(message_buffer); i++)
    /*$ inv
      i <= 136u64;
    $*/
    {
        // some "random" stuff, doesn't really matter
        /*$ extract Owned<uint8_t>, i; $*/
        message_buffer[i] = (uint8_t)((13ull + 31ull * i) & 0xffull);
    }
    #endif
    #if 0
    XmssBuffer message = {sizeof(message_buffer), message_buffer};
    #endif

    // Sign the message
    /*$ assert(is_null(signature_blob)); $*/
    /*$ assert(success != 0u8); $*/
    success = success && XMSS_OKAY == xmss_sign_message(&signature_blob, key_context, &message);
    /*$ assert(!is_null(signature_blob)); $*/

    // Verify that the signature verifies
    signature = xmss_get_signature_struct(signature_blob);
    success = success && XMSS_OKAY == xmss_verification_init(&verification_ctx, &exported_public_key, signature,
        signature_blob->data_size);
    #if 1
    success = success && XMSS_OKAY == xmss_verification_update(&verification_ctx, message.data, message.data_size,
        &part_verify);
    success = success && part_verify == message.data;
    success = success && XMSS_OKAY == xmss_verification_check(&verification_ctx, &exported_public_key);
    // redundant, for fault tolerance
    success = success && XMSS_OKAY == xmss_verification_check(&verification_ctx, &exported_public_key);
    #endif

    #if 0
    // Verify message with different "corner case" part sizes (block size SHA256: 64, SHAKE256/256: 136)
    // We'll test every combination of first part size + part size for the remainder (i.e., this is 400+ test cases).
    size_t part_sizes[] = {
        0,
        1,
        2,
        64 - 2,
        64 - 1,
        64,
        64 + 1,
        64 + 2,
        136 - 2,
        136 - 1,
        136,
        136 + 1,
        136 + 2,
        2 * 64 - 2,
        2 * 64 - 1,
        2 * 64,
        2 * 64 + 1,
        2 * 64 + 2,
        2 * 136 - 2,
        2 * 136 - 1,
        2 * 136,
        2 * 136 + 1,
        2 * 136 + 2,
        sizeof(message_buffer) - 2,
        sizeof(message_buffer) - 1,
    };
    for (size_t first_index = 0; first_index < sizeof(part_sizes) / sizeof(size_t); ++first_index) {
        // We need to skip size 0 for the remaining parts
        for (size_t other_index = 1; other_index < sizeof(part_sizes) / sizeof(size_t); ++other_index) {
            const uint8_t *part = message.data;
            size_t remaining = message.data_size;
            // size of the first part
            size_t part_size = part_sizes[first_index];

            success = success && XMSS_OKAY == xmss_verification_init(&verification_ctx, &exported_public_key, signature,
                signature_blob->data_size);
            while (remaining > 0) {
                if (part_size > remaining) {
                    // we've reached the end, this is the final part
                    part_size = remaining;
                }

                success = success && XMSS_OKAY == xmss_verification_update(&verification_ctx, part, part_size,
                    &part_verify);
                success = success && part_verify == part;

                part += part_size;
                remaining -= part_size;
                // size of the remaining parts, if any
                part_size = part_sizes[other_index];
            }
            success = success && XMSS_OKAY == xmss_verification_check(&verification_ctx, &exported_public_key);
            // redundant, for fault tolerance
            success = success && XMSS_OKAY == xmss_verification_check(&verification_ctx, &exported_public_key);
        }
    }
    #endif

    free(signature_blob);
    free(keygen_context);
    xmss_free_key_context(key_context);
    free(public_key_blob);
    free(stateless_blob);
    free(stateful_blob);
    free(context_ptr_dynamic);
    free(internal_cache);
    free(generation_cache);

    return success;
}
#endif

#if !defined(NO_XMSS)
static bool xmss_verify_signature(XmssPublicKey *exported_public_key, uint8_t *msg, size_t msg_size, XmssSignatureBlob *signature_blob)
/*$
  requires
    take epki = Owned<XmssPublicKey>(exported_public_key);
    take mi = Array_u8(msg, msg_size);
    take sbi = Owned<XmssSignatureBlob>(signature_blob);

  ensures
    take epko = Owned<XmssPublicKey>(exported_public_key);
    take mo = Array_u8(msg, msg_size);
    take sbo = Owned<XmssSignatureBlob>(signature_blob);
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

#define MEASURE_SIZE (32)
/*$ function (u64) MEASURE_SIZE() $*/
static
uint64_t c_MEASURE_SIZE() /*$ cn_function MEASURE_SIZE; $*/ { return MEASURE_SIZE; }

#if defined(WITH_ATTEST) || defined(CN_ENV)
// must go in special protected storage (writable only by firmware/hardware)
static byte last_measure[MEASURE_SIZE];  // initial contents unimportant
#if defined(NO_XMSS)
static bool public_key;
static bool xmss_signature;
#else
static XmssPublicKey public_key;
static XmssSignatureBlob xmss_signature;
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
  accesses xmss_signature;
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

#if defined(NO_XMSS)
  // apply SHA-256 to region
  SHA256((byte *)start_address,region_size,&last_measure[0]);

  // compare measure to expected measure (if it was provided)
  if ((expected_measure_ != NULL)
      &&
      (memcmp(last_measure,expected_measure_,MEASURE_SIZE) != 0))
    return HASH_MISMATCH;
#else
  if (!xmss_verify_signature(&public_key, start_address, region_size, &xmss_signature)) {
    return HASH_MISMATCH;
  }
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
