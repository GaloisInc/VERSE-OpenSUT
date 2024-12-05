#pragma once

#include <stdint.h>

#define KEY_ID_SIZE 1
#define CHALLENGE_SIZE 32
#define RESPONSE_SIZE 32
#define SECRET_KEY_SIZE 32

#define NUM_SECRET_KEYS 2
const uint8_t* get_mission_key(uint8_t key_id);
