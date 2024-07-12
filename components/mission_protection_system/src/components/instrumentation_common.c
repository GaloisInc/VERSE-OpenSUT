// VERSE OpenSUT Mission Protection System (MPS)

// Copyright 2021, 2022, 2023 Galois, Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "instrumentation.h"

void instrumentation_init(struct instrumentation_state *state) {
  state->maintenance = 1;
  // test_reading and test_complete were not previously initialized
  zero_u32_arr(state->reading, NTRIP);
  zero_u32_arr(state->test_reading, NTRIP);
  zero_u32_arr(state->setpoints, NTRIP);
  zero_u8_arr(state->sensor_trip, NTRIP);
  zero_u8_arr(state->mode, NTRIP);
  state->test_complete = 0;
}
