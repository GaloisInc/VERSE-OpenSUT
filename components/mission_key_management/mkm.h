#pragma once

#include <stdint.h>

#define NUM_SECRET_KEYS 2
#define SECRET_KEY_SIZE 32
const uint8_t* get_mission_key(uint8_t key_id);
