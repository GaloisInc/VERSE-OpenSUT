#pragma once

#ifndef CN_ENV
# include <mavlink/mavlink_types.h>
#else
# include "cn_mavlink_stubs.h"
#endif

void handle_message(const mavlink_message_t* msg);
