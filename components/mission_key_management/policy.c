#include <stddef.h>
#include <string.h>
#include "policy.h"
#include "hmac_sha256.h"

#ifndef CN_ENV
# include <stdio.h>
#else
# include "cn_stubs.h"
#endif

#define MAX_POLICY_TABLE_LEN 32
static struct policy_entry policy_table[MAX_POLICY_TABLE_LEN] = {0};
static size_t policy_table_len = 0;

static const uint8_t hmac_key[HMAC_KEY_SIZE] = "shared key for hmac attestations";

int policy_add(
        const uint8_t key_id[KEY_ID_SIZE],
        const uint8_t measure[MEASURE_SIZE],
        const uint8_t key[KEY_SIZE]) {
    if (policy_table_len >= MAX_POLICY_TABLE_LEN) {
        return -1;
    }

    struct policy_entry* p = &policy_table[policy_table_len];

    memcpy(p->key_id, key_id, KEY_ID_SIZE);
    memcpy(p->measure, measure, MEASURE_SIZE);
    memcpy(p->key, key, KEY_SIZE);

    ++policy_table_len;

    return 0;
}

// Check whether `measure` and `hmac` constitute a valid attestation for
// `nonce` with a proper signature from `hmac_key`.  Returns 1 if the
// attestation is valid and 0 otherwise.
static int check_hmac(const uint8_t nonce[NONCE_SIZE],
        const uint8_t measure[MEASURE_SIZE], const uint8_t hmac[HMAC_SIZE]) {
    uint8_t hmac_message[MEASURE_SIZE + NONCE_SIZE] = {0};
    memcpy(hmac_message, measure, MEASURE_SIZE);
    memcpy(hmac_message + MEASURE_SIZE, nonce, NONCE_SIZE);
    uint8_t correct_hmac[HMAC_SIZE] = {0};
    hmac_sha256(hmac_key, sizeof(hmac_key),
            hmac_message, sizeof(hmac_message),
            correct_hmac);
    if (memcmp(hmac, correct_hmac, HMAC_SIZE) != 0) {
        return 0;
    }
    return 1;
}

const uint8_t* policy_match_one(const struct policy_entry* p,
        uint8_t key_id[KEY_ID_SIZE], uint8_t measure[MEASURE_SIZE]) {
    if (memcmp(p->key_id, key_id, KEY_ID_SIZE) != 0) {
        return NULL;
    }
    if (memcmp(p->measure, measure, MEASURE_SIZE) != 0) {
        return NULL;
    }

    return p->key;
}

const uint8_t* policy_match(uint8_t key_id[KEY_ID_SIZE], uint8_t nonce[NONCE_SIZE],
        uint8_t measure[MEASURE_SIZE], uint8_t hmac[HMAC_SIZE]) {
    // First, check that the attestation is valid and correctly signed.  If it
    // isn't, then no policy entry will match.
    if (!check_hmac(nonce, measure, hmac)) {
        fprintf(stderr, "policy_match: bad hmac\n");
        return NULL;
    }

    // Now check each policy entry in turn to find one that matches.
    for (size_t i = 0; i < policy_table_len; ++i) {
        const uint8_t* key = policy_match_one(&policy_table[i], key_id, measure);
        if (key != NULL) {
            fprintf(stderr, "policy_match: entry %d matches request\n", (int)i);
            return key;
        }
    }
    fprintf(stderr, "policy_match: no match\n");
    return NULL;
}
