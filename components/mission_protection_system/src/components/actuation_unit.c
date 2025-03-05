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

#include "common.h"
#include "platform.h"
#include "actuation_logic.h"

#ifdef PLATFORM_HOST
#if !WAR_NO_VARIADICS
#include <stdio.h>
#endif
#else
#include "printf.h"
#endif

#define VOTE_I(_v, _i) (((_v) >> (_i)) & 0x1)

/*@requires \valid(&trip[0..2][0..3]);
  @requires \valid(&trip_test[0..2][0..3]);
  @assigns (trip[0..2][0..3]);
  @assigns (trip_test[0..2][0..3]);
*/
static int
actuation_logic_collect_trips(uint8_t logic_no, int do_test, uint8_t trip[3][4], uint8_t trip_test[3][4])
/*$
  //accesses core;
  requires
    take tin = each(u64 i; i < 3u64) {Block<uint8_t[4]>(array_shift(trip, i))};
    take ttestin = each(u64 i; i < 3u64) {Block<uint8_t[4]>(array_shift(trip_test, i))};
    take ci = Owned<struct core_state>(&core);
    core_state_ok(ci);
  ensures
    take tout = each(u64 i; i < 3u64) {Owned<uint8_t[4]>(array_shift(trip, i))};
    take ttestout = each(u64 i; i < 3u64) {Owned<uint8_t[4]>(array_shift(trip_test, i))};
    take co = Owned<struct core_state>(&core);
    core_state_ok(co);
$*/
{
    int err = 0;
    uint8_t test_div[2];
    get_test_instrumentation(test_div);

    err |= read_instrumentation_trip_signals(trip);

    #if !WAR_NESTED_ARRAYS
    /*@ loop invariant 0 <= i <= NINSTR;
      @ loop assigns i;
      @ loop assigns trip[0..2][0..3];
      @ loop assigns trip_test[0..2][0..3];
    */
    for (int i = 0; i < NINSTR; ++i) {
        /*@ loop invariant 0 <= c <= NTRIP;
          @ loop assigns c;
          @ loop assigns trip[0..2][i];
          @ loop assigns trip_test[0..2][i];
        */
        for(int c = 0; c < NTRIP; ++c) {
            uint8_t test_signal = (i == test_div[0] || i == test_div[1]);
            if (do_test) {
                trip_test[c][i] = (trip[c][i] & test_signal) != 0;
                trip[c][i] &= !test_signal;
            } else if (!VALID(trip[c][i])) {
                trip[c][i] = 0;
            }
        }
    }
    #else
    /*@ loop invariant 0 <= c <= NTRIP;
      @ loop assigns c;
      @ loop assigns trip[0..2][i];
      @ loop assigns trip_test[0..2][i];
    */
    for(int c = 0; c < NTRIP; ++c)
    /*$ inv 0i32 <= c; c <= 3i32;
        take tripinv = Owned<uint8_t[3][4]>(trip);

        take triptestinvi = each(u64 i; i < 3u64 && i > (u64)c) {Block<uint8_t[4]>(array_shift<uint8_t[4]>(trip_test, i))};
        //take triptestinvcur = each(u64 i; i < 4u64) {Block<uint8_t>(array_shift<uint8_t[4]>(trip_test, c))};
        take triptestinvcur = Block<uint8_t[4]>(array_shift<uint8_t[4]>(trip_test, c));
        take triptestinvo = each(u64 i; i < (u64)c) {Owned<uint8_t[4]>(array_shift<uint8_t[4]>(trip_test, i))};
        {trip} unchanged;
        {trip_test} unchanged;
        {&test_div} unchanged;
        {&core} unchanged;
    $*/
    {
        /*$ extract Block<uint8_t[4]>, (u64)c; $*/
        /*$ extract Owned<uint8_t[4]>, (u64)c; $*/
        /*@ loop invariant 0 <= i <= NINSTR;
          @ loop assigns i;
          @ loop assigns trip[0..2][0..3];
          @ loop assigns trip_test[0..2][0..3];
        */
        for (int i = 0; i < NINSTR; ++i)
        /*$ inv 0i32 <= i; i <= 4i32;
            0i32 <= c; c < 3i32;
            take tripinv = Owned<uint8_t[3][4]>(trip);

            take triptestinvlo = each(u64 j; j < (u64)c) {Owned<uint8_t[4]>(array_shift<uint8_t[4]>(trip_test, j))};
            //take triptestinvhi = each(u64 j; j < 3u64 && j >= (u64)c) {Block<uint8_t[4]>(array_shift(trip_test, j))};
            take triptestinvhi = each(u64 j; j < 3u64 && j >= (u64)c) {Block<uint8_t[4]>(array_shift<uint8_t[4]>(trip_test, j))};
            take triptestinvcurlo = each(u64 j; j < 4u64 && j < (u64)i) {Owned<uint8_t>(array_shift<uint8_t>(array_shift<uint8_t[4]>(trip_test, c), j))};
            take triptestinvcurhi = each(u64 j; j < 4u64 && j >= (u64)i) {Block<uint8_t>(array_shift<uint8_t>(array_shift<uint8_t[4]>(trip_test, c), j))};

            {trip} unchanged;
            {trip_test} unchanged;
            {&test_div} unchanged;
            {&c} unchanged;
            {&core} unchanged;
        $*/
        {
 
            uint8_t test_signal = (i == test_div[0] || i == test_div[1]);
            if (do_test) {
                trip_test[c][i] = (trip[c][i] & test_signal) != 0;
                trip[c][i] &= !test_signal;
            } else if (!VALID(trip[c][i])) {
                trip[c][i] = 0;
            }
        }
    }
    #endif

    return err;
}


/*@ requires \valid(&trips[0..2][0..3]);
  @ requires \valid(trips + (0..2));
  @ assigns \nothing;
*/
static uint8_t
actuate_device(uint8_t device, uint8_t trips[3][4], int old)
/*$
  requires
    take tin = Owned<uint8_t[3][4]>(trips);
    device < NDEV();
  ensures
    take tout = Owned<uint8_t[3][4]>(trips);
$*/
{
    uint8_t res = 0;
    if (device == 0) {
        res = Actuate_D0(trips, old);
    } else {
        res = Actuate_D1(trips, old);
    }
    DEBUG_PRINTF(("<actuation_unit.c> actuate_device: device=0x%X, old=0x%X, out=0x%X,trips=[\n", device, old, res));
    /*@ loop assigns i; */
    for (int i = 0; i < 3; ++i)
    /*$ inv (i <= 3i32) && (0i32 <= i);
        take tinv = each(u64 j; j < 3u64) {Owned<uint8_t[4]>(array_shift(trips, j))};
        {trips} unchanged;
    $*/
    {
        DEBUG_PRINTF(("["));
        /*@ loop assigns div; */
        for (int div = 0; div < 4; ++div)
        /*$ inv div <= 4i32; 0i32 <= div;
            take tinv2 = each(u64 k; k < 3u64) {Owned<uint8_t[4]>(array_shift(trips, k))};
            {trips} unchanged;
            0i32 <= i && i < 3i32;
        $*/
        {
        DEBUG_PRINTF(("%u,",trips[i][div]));
        }
        DEBUG_PRINTF(("],"));
    }
    DEBUG_PRINTF(("]\n"));
    return res;
}

/*@requires \valid(state);
  @requires logic_no < NVOTE_LOGIC;
  @requires device < NDEV;
  @requires \valid(trip + (0..2));
  @requires \valid(trip_test + (0..2));
  @requires \valid(&trip[0..2][0..3]);
  @requires \valid(&trip_test[0..2][0..3]);
  @assigns state->vote_actuate[device];
  @assigns core.test.actuation_old_vote;
  @assigns core.test.test_actuation_unit_done[logic_no];
*/
static void
actuation_logic_vote_trips(uint8_t logic_no, int do_test, uint8_t device, uint8_t trip[3][4], uint8_t trip_test[3][4], struct actuation_logic *state)
/*$
  //accesses core;
  requires
    take sin = Owned(state);
    take tin = Owned<uint8_t[3][4]>(trip);
    take ttestin = each(u64 i; i < 3u64) {Owned<uint8_t[4]>(array_shift(trip_test, i))};
    logic_no < NVOTE_LOGIC();
    device < NDEV();
    take ci = Owned<struct core_state>(&core);
    core_state_ok(ci);
  ensures
    take sout = Owned(state);
    take tout = Owned<uint8_t[3][4]>(trip);
    take ttestout = each(u64 i; i < 3u64) {Owned<uint8_t[4]>(array_shift(trip_test, i))};
    take co = Owned<struct core_state>(&core);
    core_state_ok(co);
$*/
{
    if (do_test && get_test_device() == device) {
        if (!is_actuation_unit_test_complete(logic_no)) {
            /*$ extract Owned<uint8_t>, (u64)device; $*/
            set_actuation_unit_test_input_vote(logic_no, state->vote_actuate[device] != 0);
            state->vote_actuate[device] = actuate_device(device, trip_test, state->vote_actuate[device] != 0);
        }
    } else {
        /*$ extract Owned<uint8_t>, (u64)device; $*/
        state->vote_actuate[device] = actuate_device(device, trip, state->vote_actuate[device] != 0);
    }
}

/*@ requires logic_no < NVOTE_LOGIC;
  @ requires \valid(state);
  @ assigns state->vote_actuate[0..1];

  @ assigns core.test.actuation_old_vote;
  @ assigns core.test.test_actuation_unit_done[logic_no];
*/
static int
actuation_logic_vote(uint8_t logic_no, int do_test, struct actuation_logic *state)
/*$
  //accesses core;
  requires
    logic_no < NVOTE_LOGIC();
    take sin = Owned(state);
    take ci = Owned<struct core_state>(&core);
    core_state_ok(ci);
  ensures
    take sout = Owned(state);
    take co = Owned<struct core_state>(&core);
    core_state_ok(co);
 $*/
{
    int err = 0;
    uint8_t trip[3][4];
    uint8_t trip_test[3][4];

    err = actuation_logic_collect_trips(logic_no, do_test, trip, trip_test);

    actuation_logic_vote_trips(logic_no, do_test, 0, trip, trip_test, state);
    actuation_logic_vote_trips(logic_no, do_test, 1, trip, trip_test, state);

    return err;
}


/*@requires \valid(cmd);
  @requires \valid(state);
  @assigns state->manual_actuate[0..1];
  @ensures -1 <= \result <= 0;
*/
static int
actuation_handle_command(uint8_t logic_no, struct actuation_command *cmd, struct actuation_logic *state)
/*$
  requires
    take cin = Owned(cmd);
    take sin = Owned(state);
  ensures
    take cout = Owned(cmd);
    take sout = Owned(state);
    return >= -1i32 && return <= 0i32;
$*/
{
    if (cmd->device <= 1) {
        /*$ extract Owned<uint8_t>, (u64)cin.device; $*/
        state->manual_actuate[cmd->device] = cmd->on;
    }
    return 0;
}

/*@requires \valid(state);
  @requires logic_no < NVOTE_LOGIC;
  @assigns state->vote_actuate[0..1];
  @assigns core.test.test_actuation_unit_done[logic_no];
  @ensures -1 <= \result <= 0;
*/
static int
output_actuation_signals(uint8_t logic_no, int do_test, struct actuation_logic *state)
/*$
  accesses core;
  //accesses device_actuation_logic;
  requires
    take dali = Owned<uint8_t[2][3]>(&device_actuation_logic);
    take sin = Owned(state);
    logic_no < NVOTE_LOGIC();
  ensures
    take sout = Owned(state);
    return >= -1i32 && return <= 0i32;
    take dalo = Owned<uint8_t[2][3]>(&device_actuation_logic);
$*/
{
    int err = 0;

    /*@ loop invariant 0 <= d <= NDEV;
      @ loop invariant -1 <= err <= 0;
      @ loop assigns d, err;
    */
    for (int d = 0; d < NDEV; ++d)
    /*$ inv d >= 0i32; d <= (i32)NDEV();
        take sinv = Owned(state);
        take dinv = Owned<uint8_t[2][3]>(&device_actuation_logic);
        {state} unchanged;
        {&device_actuation_logic} unchanged;
        {logic_no} unchanged;
        -1i32 <= err; err <= 0i32;
    $*/
    {
        /*$ extract Owned<uint8_t>, (u64)d; $*/
        uint8_t on = state->vote_actuate[d] || state->manual_actuate[d];
        if (!do_test || !is_actuation_unit_test_complete(logic_no)) {
            err |= set_output_actuation_logic(logic_no, d, BIT(do_test, on));
        }
    }
    if (do_test && !is_actuation_unit_test_complete(logic_no)) {
        // Reset internal state
        /*$ extract Owned<uint8_t>, 0u64; $*/
        state->vote_actuate[0] = 0;
        /*$ extract Owned<uint8_t>, 1u64; $*/
        state->vote_actuate[1] = 0;
        set_actuation_unit_test_complete(logic_no, 1);
    }

    return err;
}

int actuation_unit_step(uint8_t logic_no, struct actuation_logic *state)
{
    int err = 0;
    uint8_t test_div[2];

    get_test_instrumentation(test_div);
    /*$ extract Owned<uint8_t>, 0u64; $*/
    /*$ instantiate 0u64; $*/
    /*$ extract Owned<uint8_t>, 1u64; $*/
    /*$ instantiate 1u64; $*/
    int do_test = logic_no == get_test_actuation_unit() &&
                  is_instrumentation_test_complete(test_div[0]) &&
                  is_instrumentation_test_complete(test_div[1]) &&
                  is_test_running();

    if (do_test && is_actuation_unit_test_complete(logic_no))
        return 0;

    if (!do_test && is_actuation_unit_test_complete(logic_no)) {
        set_output_actuation_logic(logic_no, get_test_device(), 0);
        set_actuation_unit_test_complete(logic_no, 0);
        return 0;
    }

    /* Read trip signals & vote */
    err |= actuation_logic_vote(logic_no, do_test, state);

    /* Handle any external commands */
    struct actuation_command cmd;
    int read_cmd = read_actuation_command(logic_no, &cmd);
    if (read_cmd > 0) {
        err |= actuation_handle_command(logic_no, &cmd, state);
    } else if (read_cmd < 0) {
        err |= -read_cmd;
    }

    /* Actuate devices based on voting and commands */
    err |= output_actuation_signals(logic_no, do_test, state);
    return err;
}
