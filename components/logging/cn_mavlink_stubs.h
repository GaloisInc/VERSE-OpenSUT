#pragma once

// CN-compatible stubs for the MAVLink functions we use.

#include <stdint.h>

// From `mavlink/mavlink_types.h`

struct __mavlink_message {
    // TODO: Make this an incomplete type.  Currently, this placeholder
    // definition is necessary because CN errors on incomplete types.
    uint8_t _dummy;
};
typedef struct __mavlink_message mavlink_message_t;

const char* _mav_payload_impl(const mavlink_message_t* msg);
#define _MAV_PAYLOAD(msg) (_mav_payload_impl(msg))

typedef enum {
	MAVLINK_TYPE_CHAR     = 0,
	MAVLINK_TYPE_UINT8_T  = 1,
	MAVLINK_TYPE_INT8_T   = 2,
	MAVLINK_TYPE_UINT16_T = 3,
	MAVLINK_TYPE_INT16_T  = 4,
	MAVLINK_TYPE_UINT32_T = 5,
	MAVLINK_TYPE_INT32_T  = 6,
	MAVLINK_TYPE_UINT64_T = 7,
	MAVLINK_TYPE_INT64_T  = 8,
	MAVLINK_TYPE_FLOAT    = 9,
	MAVLINK_TYPE_DOUBLE   = 10
} mavlink_message_type_t;

#define MAVLINK_MAX_FIELDS 64

typedef struct __mavlink_field_info {
	const char *name;                 // name of this field
        const char *print_format;         // printing format hint, or NULL
        mavlink_message_type_t type;      // type of this field
        unsigned int array_length;        // if non-zero, field is an array
        unsigned int wire_offset;         // offset of each field in the payload
        unsigned int structure_offset;    // offset in a C structure
} mavlink_field_info_t;

// note that in this structure the order of fields is the order
// in the XML file, not necessary the wire order
typedef struct __mavlink_message_info {
	uint32_t msgid;                                        // message ID
	const char *name;                                      // name of the message
	unsigned num_fields;                                   // how many fields in this message
	mavlink_field_info_t fields[MAVLINK_MAX_FIELDS];       // field information
} mavlink_message_info_t;

struct __mavlink_status {
    // TODO: Make this an incomplete type.  Currently, this placeholder
    // definition is necessary because CN errors on incomplete types.
    uint8_t _dummy;
};
typedef struct __mavlink_status  mavlink_status_t;


// From `mavlink/mavlink_get_info.h`
const mavlink_message_info_t *mavlink_get_message_info(const mavlink_message_t *msg);

// From `mavlink/protocol.h`
uint8_t mavlink_parse_char(uint8_t chan, uint8_t c, mavlink_message_t* r_message, mavlink_status_t* r_mavlink_status);

extern const unsigned MAVLINK_MSG_ID_GLOBAL_POSITION_INT;
