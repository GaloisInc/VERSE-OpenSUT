#pragma once

// CN-compatible stubs for the MAVLink functions we use.

#include <stdint.h>
#include <mavlink/mavlink_types.h>

// From `mavlink/mavlink_get_info.h`
const mavlink_message_info_t *mavlink_get_message_info(const mavlink_message_t *msg);

// From `mavlink/protocol.h`
uint8_t mavlink_parse_char(uint8_t chan, uint8_t c, mavlink_message_t* r_message, mavlink_status_t* r_mavlink_status);

extern const unsigned MAVLINK_MSG_ID_GLOBAL_POSITION_INT;
