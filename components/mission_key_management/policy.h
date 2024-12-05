#pragma once

#include <stdint.h>

#define KEY_ID_SIZE 1
#define NONCE_SIZE 16
#define MEASURE_SIZE 32
#define HMAC_SIZE 32
#define HMAC_KEY_SIZE 32
#define KEY_SIZE 32

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

// Look for a policy entry matching the given key ID, nonce/challenge, measure,
// and attestation HMAC.  If a matching entry is found, this returns a pointer
// to the secret key from that entry; otherwise, it returns NULL.
const uint8_t* policy_match(uint8_t key_id[KEY_ID_SIZE], uint8_t nonce[NONCE_SIZE],
        uint8_t measure[MEASURE_SIZE], uint8_t hmac[HMAC_SIZE]);
