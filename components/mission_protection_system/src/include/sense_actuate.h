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

#ifndef SENSE_ACTUATE_H_
#define SENSE_ACTUATE_H_

#include "common.h"
#include "instrumentation.h"
#include "actuation_logic.h"

/* Initialize state for core `core_id`.
 * @requires instrumentation is an array of NINSTRUMENTATION/NCORE_ID instrumentation structs
 * @requires actuation_logic is an array of NACTUATION_LOGIC/NCORE_ID actuation_logic structs
 * @returns < 0 on error
 */
int sense_actuate_init(int core_id,
                       struct instrumentation_state *instrumentation,
                       struct actuation_logic *actuation);
/*$ spec sense_actuate_init(i32 core_id, pointer instrumentation, pointer actuation);
  requires take ii = each(u64 j; j >= 0u64 && j < 2u64) {Block<struct instrumentation_state>(array_shift(instrumentation,j))};
      take ai = Block<struct actuation_logic>(actuation);

  ensures take io = each(u64 j; j >= 0u64 && j < 2u64) {Owned<struct instrumentation_state>(array_shift(instrumentation,j))};
      take ao = Owned<struct actuation_logic>(actuation);
$*/

/* Advance state for core `core_id`.
 * @requires instrumentation is an array of NINSTRUMENTATION/NCORE_ID instrumentation structs
 * @requires actuation_logic is an array of NACTUATION_LOGIC/NCORE_ID actuation_logic structs
 * @returns < 0 on error
 */
int sense_actuate_step_0(struct instrumentation_state *instrumentation,
                         struct actuation_logic *actuation);
/*$ spec sense_actuate_step_0(pointer instrumentation, pointer actuation);
  requires take ii = each(u64 j; j < 2u64) {Owned<struct instrumentation_state>(array_shift(instrumentation,j))};
      take ai = Owned<struct actuation_logic>(actuation);
      take ci = Owned<struct core_state>(&core);
      core_state_ok(ci);

  ensures take io = each(u64 j; j < 2u64) {Owned<struct instrumentation_state>(array_shift(instrumentation,j))};
      take ao = Owned<struct actuation_logic>(actuation);
      take co = Owned<struct core_state>(&core);
      core_state_ok(co);
$*/

int sense_actuate_step_1(struct instrumentation_state *instrumentation,
                         struct actuation_logic *actuation);
/*$ spec sense_actuate_step_1(pointer instrumentation, pointer actuation);
  requires take ii = each(u64 j; j < 2u64) {Owned<struct instrumentation_state>(array_shift(instrumentation,j))};
      take ai = Owned<struct actuation_logic>(actuation);
      take ci = Owned<struct core_state>(&core);
      core_state_ok(ci);

  ensures take io = each(u64 j; j < 2u64) {Owned<struct instrumentation_state>(array_shift(instrumentation,j))};
      take ao = Owned<struct actuation_logic>(actuation);
      take co = Owned<struct core_state>(&core);
      core_state_ok(co);
$*/

#endif // SENSE_ACTUATE_H_
