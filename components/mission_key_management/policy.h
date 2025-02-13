#pragma once

#ifndef CN_ENV
#include <stdint.h>
#endif

#define KEY_ID_SIZE 1
#define NONCE_SIZE 16
#define MEASURE_SIZE 32
#define HMAC_SIZE 32
#define HMAC_KEY_SIZE 32
#define KEY_SIZE 32

#if ! defined(CN_TEST) 
// This is the idiomatic CN lifting of macro constants, per 
// https://rems-project.github.io/cn-tutorial/getting-started/style-guide/#constants

/*$ function (u64) KEY_ID_SIZE () $*/
static uint64_t c_KEY_ID_SIZE() /*$ cn_function KEY_ID_SIZE; $*/ { return KEY_ID_SIZE; }
/*$ function (u64) NONCE_SIZE () $*/
static uint64_t c_NONCE_SIZE() /*$ cn_function NONCE_SIZE; $*/ { return NONCE_SIZE; }
/*$ function (u64) MEASURE_SIZE () $*/
static uint64_t c_MEASURE_SIZE() /*$ cn_function MEASURE_SIZE; $*/ { return MEASURE_SIZE; }
/*$ function (u64) HMAC_SIZE () $*/
static uint64_t c_HMAC_SIZE() /*$ cn_function HMAC_SIZE; $*/ { return HMAC_SIZE; }
/*$ function (u64) HMAC_KEY_SIZE () $*/
static uint64_t c_HMAC_KEY_SIZE() /*$ cn_function HMAC_KEY_SIZE; $*/ { return HMAC_KEY_SIZE; }
/*$ function (u64) KEY_SIZE () $*/
static uint64_t c_KEY_SIZE() /*$ cn_function KEY_SIZE; $*/ { return KEY_SIZE; }
#else 
// TODO: Have to hardcode the values as CN test doesn't support cn_function :(
/*$ function (u64) KEY_ID_SIZE ()   { 1u64} $*/
/*$ function (u64) NONCE_SIZE ()    {16u64} $*/
/*$ function (u64) MEASURE_SIZE ()  {32u64} $*/
/*$ function (u64) HMAC_SIZE ()     {32u64} $*/
/*$ function (u64) HMAC_KEY_SIZE () {32u64} $*/
/*$ function (u64) KEY_SIZE ()      {32u64} $*/
#endif 

#define ALIGN_AS_POINTER _Alignas(_Alignof(void*))

// A single entry in the MKM policy.  Each entry consists of a set of criteria
// and a key.  For each request, the MKM server looks for a policy entry where
// all criteria match the request, and if it finds one, it sends the key
// associated with that entry.
struct policy_entry {
    // Expected measure.  The measure included in the attestation must match
    // this value for the policy entry to apply.
    ALIGN_AS_POINTER uint8_t measure[MEASURE_SIZE];
    // Secret key to send if the policy entry matches.
    ALIGN_AS_POINTER uint8_t key[KEY_SIZE];
    // Key ID.  This must match the client's requested key ID for the policy
    // entry to apply.
    ALIGN_AS_POINTER uint8_t key_id[KEY_ID_SIZE];
};

// Add an entry to the policy table.  Returns 0 on success and -1 on failure.
int policy_add(
        const uint8_t key_id[KEY_ID_SIZE],
        const uint8_t measure[MEASURE_SIZE],
        const uint8_t key[KEY_SIZE]);
// TODO: can't write a spec here thanks to #371

// Look for a policy entry matching the given key ID, nonce/challenge, measure,
// and attestation HMAC.  If a matching entry is found, this returns a pointer
// to the secret key from that entry; otherwise, it returns NULL.
const uint8_t* policy_match(uint8_t key_id[KEY_ID_SIZE], uint8_t nonce[NONCE_SIZE],
        uint8_t measure[MEASURE_SIZE], uint8_t hmac[HMAC_SIZE]);
