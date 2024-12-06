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
#include "platform.h"
#include "common.h"
#include "core.h"
#include <string.h>

#define TRIP_I(_v, _i) (((_v) >> (_i)) & 0x1)

/*@requires div < NINSTR;
  @requires \valid(state);
  @requires \valid(state->reading + (0.. NTRIP-1));
  @requires \valid(state->test_reading + (0.. NTRIP-1));
  @requires \valid(state->setpoints + (0.. NTRIP-1));
  @requires \valid(state->sensor_trip + (0.. NTRIP-1));
  @assigns state->reading[0.. NTRIP-1];
  @assigns state->test_reading[0.. NTRIP-1];
  @assigns state->sensor_trip[0.. NTRIP-1];
  @ensures -1 <= \result <= 0;
*/
static int instrumentation_step_trip(uint8_t div,
                                     int do_test,
                                     struct instrumentation_state *state)
/*$
    requires div < NINSTR();
      take si = Owned<struct instrumentation_state>(state);
      //take ci = Owned<struct core_state>(&core);
    ensures take so = Owned<struct instrumentation_state>(state);
      -1i32 <= return; return <= 0i32;
      si.mode == so.mode;
      //take co = Owned<struct core_state>(&core);
$*/
{
  int err = 0;

  if (do_test) {
    /*$ extract Owned<uint32_t>, (u64)T(); $*/
    err |= read_test_instrumentation_channel(div, T, &state->test_reading[T]);
    /*$ extract Owned<uint32_t>, (u64)P(); $*/
    err |= read_test_instrumentation_channel(div, P, &state->test_reading[P]);
    /*$ extract Owned<uint32_t>, (u64)S(); $*/
    state->test_reading[S] = Saturation(state->test_reading[T], state->test_reading[P]);
  } else {
    /*$ extract Owned<uint32_t>, (u64)T(); $*/
    err |= read_instrumentation_channel(div, T, &state->reading[T]);
    /*$ extract Owned<uint32_t>, (u64)P(); $*/
    err |= read_instrumentation_channel(div, P, &state->reading[P]);
    /*$ extract Owned<uint32_t>, (u64)S(); $*/
    state->reading[S] = Saturation(state->reading[T], state->reading[P]);
  }

  uint8_t new_trips = 0;

  if (do_test) {
    uint32_t setpoints[3];
    err |= get_instrumentation_test_setpoints(div, &setpoints[0]);
    new_trips = Generate_Sensor_Trips(state->test_reading, setpoints);
  } else {
    new_trips = Generate_Sensor_Trips(state->reading, state->setpoints);
  }

  /*@loop invariant 0 <= i && i <= NTRIP;
    @loop assigns i;
    @loop assigns state->sensor_trip[0.. NTRIP-1];
  */
  for (int i = 0; i < NTRIP; ++i)
  /*$ inv i <= (i32)NTRIP();
          0i32 <= i;
          take sinv = Owned<struct instrumentation_state>(state);
          //ptr_eq(state, {state}@start);
          //{&state} unchanged;
          //{(*state).mode} unchanged;
          err == -1i32 || err == 0i32;
  $*/
  {
    /*$ extract Owned<uint8_t>, (u64)i; $*/
#if !WAR_CN_233
    state->sensor_trip[i] = TRIP_I(new_trips, i);
#else
    state->sensor_trip[i] = (uint8_t)TRIP_I((uint32_t)new_trips, i);
#endif
  }

  return err;
}

/*@requires \valid(i_cmd);
  @requires \valid(state);
  @requires state->mode[0] \in {0,1,2};
  @requires state->mode[1] \in {0,1,2};
  @requires state->mode[2] \in {0,1,2};
  @assigns state->maintenance, state->mode[0..2], state->setpoints[0..2];
  @ensures -1 <= \result <= 0;
  @ensures state->mode[0] \in {0,1,2};
  @ensures state->mode[1] \in {0,1,2};
  @ensures state->mode[2] \in {0,1,2};
*/
static int instrumentation_handle_command(uint8_t div,
                                          struct instrumentation_command *i_cmd,
                                          struct instrumentation_state *state)
/*$ requires take ic_in = Owned<struct instrumentation_command>(i_cmd);
    requires take s_in = Owned<struct instrumentation_state>(state);

    requires each(u64 i; 0u64 <= i && i < (u64)NTRIP()) {s_in.mode[i] < NMODES()};
    ensures take ic_out = Owned<struct instrumentation_command>(i_cmd);
    ensures take s_out = Owned<struct instrumentation_state>(state);
    ensures return >= -1i32; return <= 0i32;
    ensures each(u64 i; 0u64 <= i && i < (u64)NTRIP()) {s_out.mode[i] < NMODES()};
$*/
{
  struct set_maintenance set_maint;
  struct set_mode set_mode;
  struct set_setpoint set_setpoint;

  switch (i_cmd->type) {
  case SET_MAINTENANCE:
    set_maint = i_cmd->cmd.maintenance;
    state->maintenance = set_maint.on;
    break;

  case SET_MODE:
    set_mode = i_cmd->cmd.mode;
    if (state->maintenance && set_mode.channel < NTRIP &&
        set_mode.mode_val < NMODES) {
      /*$ extract Owned<uint8_t>, (u64)ic_in.cmd.mode.channel; $*/
      state->mode[set_mode.channel] = set_mode.mode_val;
    }
    break;

  case SET_SETPOINT:
    set_setpoint = i_cmd->cmd.setpoint;
    if (state->maintenance && set_setpoint.channel < NTRIP) {
      /*$ extract Owned<uint32_t>, (u64)ic_in.cmd.setpoint.channel; $*/
      state->setpoints[set_setpoint.channel] = set_setpoint.val;
    }
    break;

  default:
    return -1;
  }

  return 0;
}

/*@ requires div < NINSTR;
  @ requires \valid(state);
  @ requires state->mode[0] \in {0,1,2};
  @ requires state->mode[1] \in {0,1,2};
  @ requires state->mode[2] \in {0,1,2};
  @ assigns core.test.test_instrumentation_done[div];
  @ ensures \result <= 0;
*/
static int instrumentation_set_output_trips(uint8_t div,
                                            int do_test,
                                            struct instrumentation_state *state)
/*$
  accesses error_instrumentation;
  accesses trip_signals;
  requires
    div < NINSTR();
    take si = Owned<struct instrumentation_state>(state);
    each(u64 i; 0u64 <= i && i < (u64)NTRIP()) {si.mode[i] < NMODES()};
    take ci = Owned<struct core_state>(&core);
  ensures
    return <= 0i32;
    take so = Owned<struct instrumentation_state>(state);
    si == so;
    take co = Owned<struct core_state>(&core);
$*/
{
  /*@ loop invariant 0 <= i <= NTRIP;
    @ loop assigns i;
  */
  for (int i = 0; i < NTRIP; ++i)
  /*$ inv 0i32 <= i;
      i <= (i32)NTRIP();
      take sinv = Owned<struct instrumentation_state>(state);
      each(u64 j; 0u64 <= j && j < (u64)NTRIP()) {sinv.mode[j] < NMODES()};
      take cinv = Owned<struct core_state>(&core);
      {state} unchanged;
      {*state} unchanged;
      {div} unchanged;
  $*/
  {
    /*$ extract Owned<uint8_t>, (u64)i; $*/
    /*$ instantiate (u64)i; $*/
    uint8_t mode = do_test ? 1 : state->mode[i];
    set_output_instrumentation_trip(div, i, BIT(do_test, Is_Ch_Tripped(mode, 0 != state->sensor_trip[i])));
  }

  if (do_test) {
    set_instrumentation_test_complete(div, 1);
  }

  return 0;
}

int instrumentation_step(uint8_t div, struct instrumentation_state *state) {
  int err = 0;

  uint8_t test_div[2];
  get_test_instrumentation(test_div);
  /*$ extract Owned<uint8_t>, 0u64; $*/
  /*$ extract Owned<uint8_t>, 1u64; $*/
  int do_test = (div == test_div[0] || div == test_div[1]) && is_test_running();

  if (do_test && is_instrumentation_test_complete(div))
    return 0;

  if (!do_test && is_instrumentation_test_complete(div)) {
    set_instrumentation_test_complete(div, 0);
  }

  /* Read trip signals & vote */
  err |= instrumentation_step_trip(div, do_test, state);

  /* Handle any external commands */
  struct instrumentation_command i_cmd;
  int read_cmd = read_instrumentation_command(div, &i_cmd);
  if (read_cmd > 0) {
    err |= instrumentation_handle_command(div, &i_cmd, state);
  } else if (read_cmd < 0) {
    err |= -read_cmd;
  }

  /* Actuate devices based on voting and commands */
  err |= instrumentation_set_output_trips(div, do_test, state);
  return err;
}
