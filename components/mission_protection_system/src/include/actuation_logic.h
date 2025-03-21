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

#ifndef ACTUATION_H_
#define ACTUATION_H_

#include "stdint.h"
#include "common.h"
#include "instrumentation.h"
#include "core.h"
#include "models.acsl"

/*@requires \valid(&trips[0.. NINSTR -1]);
  @assigns \nothing;
  @ensures (\result != 0) <==> Coincidence_2_4(trips);
*/
uint8_t Coincidence_2_4(uint8_t trips[4]);

/*@requires \valid(&trips[0.. NTRIP - 1][0.. NINSTR - 1]);
  @requires \valid(trips + (0.. NTRIP-1));
  @assigns \nothing;
  @ensures (\result != 0) <==> Actuate_D0(&trips[T][0], &trips[P][0], &trips[S][0], old != 0);
*/
uint8_t Actuate_D0(uint8_t trips[3][4], uint8_t old);
/*$ spec Actuate_D0(pointer trips, u8 old);
  // @PropertyClass: P3-SOP
  // @PropertyClass: P5-UDFunc
    requires take tin = each(u64 i; i < 3u64) {Owned<uint8_t[4]>(array_shift(trips, i))};
    ensures take tout = each(u64 i; i < 3u64) {Owned<uint8_t[4]>(array_shift(trips, i))};
      (return != 0u8) == Actuate_D0(tin[(u64)T()], tin[(u64)P()], tin[(u64)S()], old != 0u8);
$*/

/*@requires \valid(&trips[0.. NTRIP-1][0.. NINSTR-1]);
  @requires \valid(trips + (0.. NTRIP-1));
  @assigns \nothing;
  @ensures (\result != 0) <==> Actuate_D1(&trips[T][0], &trips[P][0], &trips[S][0], old != 0);
*/
uint8_t Actuate_D1(uint8_t trips[3][4], uint8_t old);
/*$ spec Actuate_D1(pointer trips, u8 old);
  // @PropertyClass: P3-SOP
  // @PropertyClass: P5-UDFunc
    requires take tin = each(u64 i; i < 3u64) {Owned<uint8_t[4]>(array_shift(trips, i))};
    ensures take tout = each(u64 i; i < 3u64) {Owned<uint8_t[4]>(array_shift(trips, i))};
      (return != 0u8) == Actuate_D1(tin[(u64)T()], tin[(u64)P()], tin[(u64)S()], old != 0u8);
$*/

struct actuation_logic {
    uint8_t vote_actuate[NDEV];
    uint8_t manual_actuate[NDEV];
};

extern struct actuation_logic actuation_logic[2];

/* The main logic of the actuation unit */

/*@requires \valid(state);
  @requires logic_no <= 1;
  @assigns state->manual_actuate[0.. NDEV-1];
  @assigns state->vote_actuate[0.. NDEV-1];
  @assigns core.test.actuation_old_vote;
  @assigns core.test.test_actuation_unit_done[logic_no];
*/
int actuation_unit_step(uint8_t logic_no, struct actuation_logic *state);
/*$ spec actuation_unit_step(u8 logic_no, pointer state);
  // @PropertyClass: P1-LAC
  // @PropertyClass: P3-SOP
  // @PropertyClass: P5-UDFunc
    requires take sin = Owned(state);
      logic_no <= 1u8;
      take ci = Owned<struct core_state>(&core);
      //take dali = Owned<uint8_t[3][2]>(&device_actuation_logic);
      core_state_ok(ci);
    ensures take sout = Owned(state);
      take co = Owned<struct core_state>(&core);
      //take dalo = Owned<uint8_t[3][2]>(&device_actuation_logic);
      core_state_ok(co);
$*/

#endif // ACTUATION_H_
