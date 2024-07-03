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

#ifndef INSTRUMENTATION_H_
#define INSTRUMENTATION_H_

#include "common.h"
#include "core.h"
#include "models.acsl"

#ifdef __cplusplus
extern "C" {
#endif

#define ShouldTrip(_vals, _setpoints, _ch) \
  ((_ch == T && _vals[T] > _setpoints[T])     \
   ||  (_ch == P && _vals[P] > _setpoints[P])          \
   ||  (_ch == S && (int)_vals[S] < (int)_setpoints[S]))

/*@ assigns \nothing; */
uint32_t Saturation(uint32_t x, uint32_t y);
/*$ spec Saturation(u32 x, u32 y);
    requires true;
    ensures true;
$*/

/*@requires \valid(vals + (0.. NTRIP-1));
  @requires \valid(setpoints + (0.. NTRIP-1));
  @assigns \nothing;
  @ensures \result == (uint8_t)Generate_Sensor_Trips(vals, setpoints);
*/
uint8_t Generate_Sensor_Trips(uint32_t vals[3], uint32_t setpoints[3]);
/*$ spec Generate_Sensor_Trips(pointer vals, pointer setpoints);
    requires
      take vin = each(u64 i; i < (u64)NTRIP()) {Owned<uint32_t>(array_shift(vals,i))};
      take sin = each(u64 j; j < (u64)NTRIP()) {Owned<uint32_t>(array_shift(setpoints,j))};
    ensures return == Generate_Sensor_Trips(vin, sin);
      take vout = each(u64 k; k < (u64)NTRIP()) {Owned<uint32_t>(array_shift(vals,k))};
      take sout = each(u64 l; l < (u64)NTRIP()) {Owned<uint32_t>(array_shift(setpoints,l))};
      vin == vout;
      sin == sout;
$*/

/*@requires \valid(vals + (0.. NTRIP-1));
  @requires \valid(setpoints + (0.. NTRIP-1));
  @requires ch < NTRIP;
  @assigns \nothing;
  @ensures \result == 0 || \result == 1;
  @ensures (\result == 1) <==> Trip(vals, setpoints, ch);
*/
uint8_t Trip(uint32_t vals[3], uint32_t setpoints[3], uint8_t ch);

/*@requires mode < NMODES;
  @requires trip <= 1;
  @assigns \nothing;
  @ensures (\result != 0) <==> Is_Ch_Tripped(mode, trip != 0);
*/
uint8_t Is_Ch_Tripped(uint8_t mode, uint8_t trip);
/*$ spec Is_Ch_Tripped(u8 mode, u8 trip);
    requires mode < NMODES();
      trip <= 1u8;
    ensures (return != 0u8) == Is_Ch_Tripped(mode, trip != 0u8);
$*/

struct instrumentation_state {
  uint32_t reading[NTRIP];
  uint32_t test_reading[NTRIP];
  uint32_t setpoints[NTRIP];
  uint8_t sensor_trip[NTRIP];
  uint8_t mode[NTRIP];
  uint8_t maintenance;
  uint8_t test_complete;
};

void instrumentation_init(struct instrumentation_state *state);
/*$ spec instrumentation_init(pointer state);
    requires take i = Block<struct instrumentation_state>(state);
    ensures take o = Owned<struct instrumentation_state>(state);
$*/

/*@requires \valid(state);
  @requires \valid(state->reading + (0.. NTRIP-1));
  @requires \valid(state->test_reading + (0.. NTRIP-1));
  @requires \valid(state->setpoints + (0.. NTRIP-1));
  @requires \valid(state->sensor_trip + (0.. NTRIP-1));
  @requires state->mode[T] \in {BYPASS, OPERATE, TRIP};
  @requires state->mode[P] \in {BYPASS, OPERATE, TRIP};
  @requires state->mode[S] \in {BYPASS, OPERATE, TRIP};
  @requires div < NTRIP;
  @assigns state->reading[0.. NTRIP-1];
  @assigns state->test_reading[0.. NTRIP-1];
  @assigns state->setpoints[0.. NTRIP-1];
  @assigns state->sensor_trip[0.. NTRIP-1];
  @assigns state->maintenance;
  @assigns state->mode[0.. NTRIP-1];
  @assigns core.test.test_instrumentation_done[div];
  @ensures state->mode[T] \in {BYPASS, OPERATE, TRIP};
  @ensures state->mode[P] \in {BYPASS, OPERATE, TRIP};
  @ensures state->mode[S] \in {BYPASS, OPERATE, TRIP};
*/
int instrumentation_step(uint8_t div, struct instrumentation_state *state);
/*$ spec instrumentation_step(u8 div, pointer state);
    requires take statein = Owned<struct instrumentation_state>(state);
      each(u64 j; j < (u64)NTRIP()) {statein.mode[j] < NMODES()};
      div < NTRIP();
    ensures
      take stateout = Owned<struct instrumentation_state>(state);
      each(u64 j; j < (u64)NTRIP()) {stateout.mode[j] < NMODES()};
$*/

#ifdef __cplusplus
}
#endif

#endif // INSTRUMENTATION_H_
