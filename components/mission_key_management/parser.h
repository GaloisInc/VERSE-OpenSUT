#pragma once

#include <stdint.h>
#include "policy.h"

// Read the next policy entry from `fd` and store it into `entry`.  Returns 1
// on success, 0 on EOF, and -1 on failure.  If an error occurs, this function
// prints to `stderr` before returning.
int parse_policy_entry(int fd, struct policy_entry* entry);
