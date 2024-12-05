#include <stddef.h>
#include <string.h>
#include <stdio.h>
#include "policy.h"

#define MAX_POLICY_TABLE_LEN 32
static struct policy_entry policy_table[MAX_POLICY_TABLE_LEN] = {0};
static size_t policy_table_len = 0;

int policy_add(
        const uint8_t key_id[KEY_ID_SIZE],
        const uint8_t measure[MEASURE_SIZE],
        const uint8_t hmac_key[HMAC_KEY_SIZE],
        const uint8_t key[KEY_SIZE]) {
    if (policy_table_len >= MAX_POLICY_TABLE_LEN) {
        return -1;
    }

    struct policy_entry* p = &policy_table[policy_table_len];

    memcpy(p->key_id, key_id, KEY_ID_SIZE);
    memcpy(p->measure, measure, MEASURE_SIZE);
    memcpy(p->hmac_key, hmac_key, HMAC_KEY_SIZE);
    memcpy(p->key, key, KEY_SIZE);

    ++policy_table_len;

    return 0;
}

const uint8_t* policy_match_one(const struct policy_entry* p,
        uint8_t key_id[KEY_ID_SIZE], uint8_t nonce[NONCE_SIZE],
        uint8_t measure[MEASURE_SIZE], uint8_t hmac[HMAC_SIZE]) {
    if (memcmp(p->key_id, key_id, KEY_ID_SIZE) != 0) {
        return NULL;
    }
    if (memcmp(p->measure, measure, MEASURE_SIZE) != 0) {
        return NULL;
    }
    // FIXME: check `hmac` against hmac of nonce + measure + hmac_key
    return p->key;
}

const uint8_t* policy_match(uint8_t key_id[KEY_ID_SIZE], uint8_t nonce[NONCE_SIZE],
        uint8_t measure[MEASURE_SIZE], uint8_t hmac[HMAC_SIZE]) {
    for (size_t i = 0; i < policy_table_len; ++i) {
        const uint8_t* key = policy_match_one(&policy_table[i],
                key_id, nonce, measure, hmac);
        if (key != NULL) {
            fprintf(stderr, "policy_match: entry %d matches request\n", (int)i);
            return key;
        }
    }
    return NULL;
}
