#include <stddef.h>
#include <string.h>

// TODO added to make verification pass 
#include <unistd.h>
#include <stdio.h>

//SYSTEM_HEADERS
// ^^^ magic string used during preprocessing - do not move / remove 

#include "policy.h"
#include "hmac_sha256.h"

#ifdef CN_ENV
# include "cn_stubs.h"
# include "cn_array_utils.h"
#endif

// TODO `Alloc` construct not supported by `cn test`
#if defined(CN_ENV) && ! defined(CN_TEST) 
# include "cn_memory.h"
#endif 

#if defined(CN_TEST) 
# define NULL ((void *)0)
#endif 

#define MAX_POLICY_TABLE_LEN 32

#if defined(CN_ENV) && ! defined(CN_TEST)
/*$ function (u64) MAX_POLICY_TABLE_LEN () $*/
static uint64_t c_MAX_POLICY_TABLE_LEN() /*$ cn_function MAX_POLICY_TABLE_LEN; $*/ { return MAX_POLICY_TABLE_LEN; }
#else 
/*$ function (u64) MAX_POLICY_TABLE_LEN ()   { 32u64} $*/
#endif 

static struct policy_entry policy_table[MAX_POLICY_TABLE_LEN] = {0};

#if ! defined(CN_ENV)
static size_t policy_table_len = 0;
#else 
// TODO required due to CN issue with size_t 
static unsigned long policy_table_len = 0;
#endif 

// `trusted_boot.c` currently uses an all-zero key for its HMACs.
static const uint8_t hmac_key[HMAC_KEY_SIZE] = {0};

int policy_add(
        const uint8_t key_id[KEY_ID_SIZE],
        const uint8_t measure[MEASURE_SIZE],
        const uint8_t key[KEY_SIZE]) 
// TODO: needed because CN test doesn't handle global arrays, see #831
#if ! defined(CN_TEST)
/*$
accesses policy_table; 
$*/
#endif 
/*$
accesses policy_table_len; 
requires 
    take Key_id_in  = ArrayOwned_u8(key_id, KEY_ID_SIZE()); 
    take Measure_in = ArrayOwned_u8(measure, MEASURE_SIZE()); 
    take Key_in     = ArrayOwned_u8(key, KEY_SIZE()); 
ensures
    take Key_id_out  = ArrayOwned_u8(key_id, KEY_ID_SIZE()); 
    take Measure_out = ArrayOwned_u8(measure, MEASURE_SIZE()); 
    take Key_out     = ArrayOwned_u8(key, KEY_SIZE()); 
$*/
{
    if (policy_table_len >= MAX_POLICY_TABLE_LEN) {
        return -1;
    }; 

    /*$ extract Owned<struct policy_entry>, policy_table_len; $*/
    struct policy_entry* p = &policy_table[policy_table_len];

    memcpy(p->key_id, key_id, KEY_ID_SIZE);
    memcpy(p->measure, measure, MEASURE_SIZE);
    memcpy(p->key, key, KEY_SIZE);

    // ++policy_table_len;
    policy_table_len++;

    return 0;
}

// Check whether `measure` and `hmac` constitute a valid attestation for
// `nonce` with a proper signature from `hmac_key`.  Returns 1 if the
// attestation is valid and 0 otherwise.
static int check_hmac(const uint8_t nonce[NONCE_SIZE],
        const uint8_t measure[MEASURE_SIZE], const uint8_t hmac[HMAC_SIZE]) 
/*$
requires 
    take Nonce_in  = ArrayOwned_u8(nonce, NONCE_SIZE()); 
    take Measure_in = ArrayOwned_u8(measure, MEASURE_SIZE()); 
    take Hmac_in = ArrayOwned_u8(hmac, HMAC_SIZE()); 
ensures 
    take Nonce_out  = ArrayOwned_u8(nonce, NONCE_SIZE()); 
    take Measure_out = ArrayOwned_u8(measure, MEASURE_SIZE()); 
    take Hmac_out = ArrayOwned_u8(hmac, HMAC_SIZE()); 
$*/
{
    uint8_t hmac_message[MEASURE_SIZE + NONCE_SIZE] = {0};
    // TODO gross hack caused by weird CN type lifting 
    uint8_t *tmp = hmac_message; 

    // TODO Should be automated 
    /*$ apply SplitAt_Owned_u8(tmp, MEASURE_SIZE() + NONCE_SIZE(), MEASURE_SIZE(), NONCE_SIZE()); $*/
    /*$ apply ViewShift_Owned_u8(tmp, tmp + MEASURE_SIZE(), MEASURE_SIZE(), NONCE_SIZE());$*/
    memcpy(hmac_message, measure, MEASURE_SIZE);
    memcpy(hmac_message + MEASURE_SIZE, nonce, NONCE_SIZE);
    /*$ apply UnViewShift_Owned_u8(tmp, tmp + MEASURE_SIZE(), MEASURE_SIZE(), NONCE_SIZE());$*/
    /*$ apply UnSplitAt_Owned_u8(tmp, MEASURE_SIZE() + NONCE_SIZE(), MEASURE_SIZE(), NONCE_SIZE()); $*/
    uint8_t correct_hmac[HMAC_SIZE] = {0};
    // TODO: 
    // hmac_sha256(hmac_key, sizeof(hmac_key),
    //         hmac_message, sizeof(hmac_message),
    //         correct_hmac);
    if (memcmp(hmac, correct_hmac, HMAC_SIZE) != 0) {
        return 0;
    }
    return 1;
}

const uint8_t* policy_match_one(const struct policy_entry* p,
        uint8_t key_id[KEY_ID_SIZE], uint8_t measure[MEASURE_SIZE]) 
/*$ 
requires 
    take P_in = Owned(p); 
    take Key_Id_in = ArrayOwned_u8(key_id, KEY_ID_SIZE()); 
    take Measure_in = ArrayOwned_u8(measure, MEASURE_SIZE()); 
ensures 
    take P_out = Owned(p); 
    take Key_Id_out = ArrayOwned_u8(key_id, KEY_ID_SIZE()); 
    take Measure_out = ArrayOwned_u8(measure, MEASURE_SIZE()); 
$*/
{
    if (memcmp(p->key_id, key_id, KEY_ID_SIZE) != 0) {
        return NULL;
    }
    if (memcmp(p->measure, measure, MEASURE_SIZE) != 0) {
        return NULL;
    }

    return p->key;
}

// TODO: can't test this function because CN test doesn't handle global arrays, see #831
#if ! defined(CN_TEST)
#if defined(CN_ENV)
const uint8_t* _TODO_CN_FAKE_policy_match(uint8_t key_id[KEY_ID_SIZE], uint8_t nonce[NONCE_SIZE],
        uint8_t measure[MEASURE_SIZE], uint8_t hmac[HMAC_SIZE]) 
#else 
const uint8_t* policy_match(uint8_t key_id[KEY_ID_SIZE], uint8_t nonce[NONCE_SIZE],
        uint8_t measure[MEASURE_SIZE], uint8_t hmac[HMAC_SIZE]) 
#endif 
/*$
accesses policy_table; 
accesses __stderr; 
accesses policy_table_len; 
requires 
    take Key_Id_in = ArrayOwned_u8(key_id, KEY_ID_SIZE()); 
    take Nonce_in = ArrayOwned_u8(nonce, NONCE_SIZE()); 
    take Measure_in = ArrayOwned_u8(measure, MEASURE_SIZE()); 
    take Hmac_in = ArrayOwned_u8(hmac, HMAC_SIZE()); 
    policy_table_len < MAX_POLICY_TABLE_LEN(); 
ensures 
    take Key_Id_out = ArrayOwned_u8(key_id, KEY_ID_SIZE()); 
    take Nonce_out  = ArrayOwned_u8(nonce, NONCE_SIZE()); 
    take Measure_out = ArrayOwned_u8(measure, MEASURE_SIZE()); 
    take Hmac_out = ArrayOwned_u8(hmac, HMAC_SIZE()); 
$*/
{
    // First, check that the attestation is valid and correctly signed.  If it
    // isn't, then no policy entry will match.
    if (!check_hmac(nonce, measure, hmac)) {
        fprintf(stderr, "policy_match: bad hmac\n");
        return NULL;
    }

    // Now check each policy entry in turn to find one that matches.
    // TODO: can't use prefix ++i due to #807 
    // for (size_t i = 0; i < policy_table_len; ++i) 
    for (size_t i = 0; i < policy_table_len; i++) 
    /*$ inv take Key_Id_inv = ArrayOwned_u8(key_id, KEY_ID_SIZE()); 
            take Nonce_inv  = ArrayOwned_u8(nonce, NONCE_SIZE()); 
            take Measure_inv = ArrayOwned_u8(measure, MEASURE_SIZE()); 
            take Hmac_inv = ArrayOwned_u8(hmac, HMAC_SIZE()); 
            0u64 <= i; i <= policy_table_len; 
            {policy_table_len} unchanged; 
            {key_id} unchanged; 
            {nonce} unchanged; 
            {measure} unchanged; 
            {hmac} unchanged; 
    $*/
    {
        /*$ extract Owned<struct policy_entry>, i; $*/
        const uint8_t* key = policy_match_one(&policy_table[i], key_id, measure);
        if (key != NULL) {
            fprintf(stderr, "policy_match: entry %d matches request\n", (int)i);
            return key;
        }
    }
    fprintf(stderr, "policy_match: no match\n");
    return NULL;
}
#endif 