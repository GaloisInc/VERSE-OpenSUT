// HARDENS Reactor Trip System (RTS)

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

#ifndef PLATFORM_H_
#define PLATFORM_H_
#include <stdint.h>

#include "common.h"
#include "core.h"
#include "instrumentation.h"
#include "actuation_logic.h"

// channel -> sensor # -> val
extern uint32_t sensors[2][2];
// channel -> sensor # -> demux output # -> val
extern uint32_t sensors_demux[2][2][2];

extern uint8_t trip_signals[NTRIP][4];
extern struct instrumentation_command inst_command_buf[4];

extern uint8_t actuator_state[NDEV];
extern uint8_t device_actuation_logic[2][NDEV];
extern struct actuation_command *act_command_buf[2];

//EI mode:
//  mode = 0 => no error
//  mode = 1 => error
//  mode = 2 => nondet error
extern uint8_t error_instrumentation_mode[NINSTR];
extern uint8_t error_instrumentation[NINSTR];
// ES ch mode:
//   mode = 0 => no error
//   mode = 1 => demux error (out 0)
//   mode = 2 => demux error (out 1)
//   mode = 3 => sensor error (error in both demux outs)
//   mode = 4 => nondet sensor error
//   mode = 5 => nondet demux error
extern uint8_t error_sensor_mode[2][2];
extern uint8_t error_sensor[2][2];
extern uint8_t error_sensor_demux[2][2][2];

#if !WAR_NO_VARIADICS
#ifdef DEBUG
#define DEBUG_PRINTF(X) printf X
#else
#define DEBUG_PRINTF(X)
#endif
#else
#define DEBUG_PRINTF(X)
#endif

#ifdef PLATFORM_HOST
#include <assert.h>
#define ASSERT(x) assert(x)
#else
#define ASSERT(x)
#endif // PLATFORM_HOST

#if defined(PLATFORM_HOST) && defined(USE_PTHREADS)
#include <pthread.h>
extern pthread_mutex_t display_mutex;
extern pthread_mutex_t mem_mutex;
#define MUTEX_LOCK(x) pthread_mutex_lock(x)
#define MUTEX_UNLOCK(x) pthread_mutex_unlock(x)
#else
#define MUTEX_LOCK(x)
#define MUTEX_UNLOCK(x)
#endif // defined(PLATFORM_HOST) && defined(USE_PTHREADS)

/////////////////////////////////////////
// Reading signals and values          //
/////////////////////////////////////////

/* @requires \valid(val);
  @requires div < NINSTR;
  @requires channel < NTRIP;
  @assigns *val;
  @ensures -1 <= \result <= 0;
  @ensures \result == 0 ==>  *val <= 0x80000000;
 */
int read_instrumentation_channel(uint8_t div, uint8_t channel, uint32_t *val);

int get_instrumentation_value(uint8_t division, uint8_t ch, uint32_t *value);
int get_instrumentation_trip(uint8_t division, uint8_t ch, uint8_t *value);
int get_instrumentation_mode(uint8_t division, uint8_t ch, uint8_t *value);
int get_instrumentation_maintenance(uint8_t division, uint8_t *value);

// Reading actuation signals
/*@ requires i <= 1;
  @ requires device < NDEV;
  @ requires \valid(value);
  @ assigns *value;
  @ ensures (\result == 0) ==> (*value == 0 || *value == 1);
  @ ensures (\result != 0) ==> (*value == \old(*value));
*/
int get_actuation_state(uint8_t i, uint8_t device, uint8_t *value);
/*$ spec get_actuation_state(u8 i, u8 device, pointer value);
    requires i <= 1u8;
             device < NDEV();
             take vin = Owned<uint8_t>(value);
    ensures take vout = Owned<uint8_t>(value);
            ((return == 0i32) ? (vout == 0u8 || vout == 1u8) :
             (vout == vin));
$*/

/* @requires \valid(&arr[0.. NTRIP-1][0.. NINSTR-1]);
  @assigns *(arr[0.. NTRIP-1]+(0.. NINSTR-1));
*/
int read_instrumentation_trip_signals(uint8_t arr[3][4]);

/////////////////////////////////////////
// Setting output signals              //
/////////////////////////////////////////

int reset_actuation_logic(uint8_t logic_no, uint8_t device_no, uint8_t reset_val);

/* @requires logic_no < NVOTE_LOGIC;
  @requires device_no < NDEV;
  @assigns \nothing; // Not entirely true, but we'll never mention that state
  @ensures -1 <= \result <= 0;
 */
int set_output_actuation_logic(uint8_t logic_no, uint8_t device_no, uint8_t on);

/* @requires division < NINSTR;
  @requires channel < NTRIP;
  @assigns \nothing; // Not entirely true, but we'll never mention that state
*/
int set_output_instrumentation_trip(uint8_t division, uint8_t channel, uint8_t val);

/*@ requires device_no <= 1;
  @ assigns \nothing;
*/
int set_actuate_device(uint8_t device_no, uint8_t on);
/*$ spec set_actuate_device(u8 device_no, u8 on);
    requires device_no <= 1u8;
    ensures true;
$*/

/////////////////////////////////////////
// Sending commands between components //
/////////////////////////////////////////
/**
 * Read RTS command from the user
 * Platform specific
 */
int read_rts_command(struct rts_command *cmd);

/* Communicate with instrumentation division */

/* @requires division < NINSTR;
  @requires \valid(cmd);
  @assigns cmd->type, cmd->cmd;
  @ensures -1 <= \result <= 1;
*/
int read_instrumentation_command(uint8_t division, struct instrumentation_command *cmd);

/* @requires division < NINSTR;
  @requires \valid(cmd);
  @assigns \nothing; // not entirely true, but we'll never mention that state
  @ensures -1 <= \result <= 0;
*/
int send_instrumentation_command(uint8_t division, struct instrumentation_command *cmd);

/**
 * Read external command, setting *cmd. Does not block.
 * Platform specific
 */
/* @requires \valid(cmd);
  @assigns cmd->on;
  @assigns cmd->device;
  @ensures -1 <= \result <= 1;
 */
int read_actuation_command(uint8_t id, struct actuation_command *cmd);

/**
 * Physically set actuator to a new value
 * Platform specific
 */
int send_actuation_command(uint8_t actuator,
                           struct actuation_command *cmd);


/////////////////////////////////////////////
// Self Test state                         //
/////////////////////////////////////////////

/*@ assigns \nothing; */
uint8_t is_test_running(void);
/*$ spec is_test_running();
    requires true;
    ensures true;
$*/

/*@ assigns \nothing; */
void set_test_running(int val);
/*$ spec set_test_running(i32 val);
    requires true;
    ensures true;
$*/

/*@ assigns \nothing;
  @ ensures \result < NDEV;
*/
uint8_t get_test_device(void);
/*$ spec get_test_device();
    requires true;
    ensures return < NDEV();
$*/

/* @ requires \valid(id) && \valid(&id[1]);
  @ assigns id[0], id[1];
  @ ensures id[0] < NINSTR;
  @ ensures id[1] < NINSTR;
*/
void get_test_instrumentation(uint8_t *id);

/* @ requires \valid(setpoints + (0.. NTRIP-1));
  @ requires id < NINSTR;
  @ assigns setpoints[0.. NTRIP-1];
  @ ensures -1 <= \result <= 0;
*/
int get_instrumentation_test_setpoints(uint8_t id, uint32_t *setpoints);

/* @ requires div < NINSTR;
  @ assigns core.test.test_instrumentation_done[div];
  @ ensures core.test.test_instrumentation_done[div] == v;
*/
void set_instrumentation_test_complete(uint8_t div, int v);

/* @ requires id < NINSTR;
  @ assigns \nothing;
*/
int is_instrumentation_test_complete(uint8_t id);

/* @ requires div < NINSTR;
  @ requires channel < NTRIP;
  @ requires \valid(val);
  @ assigns *val;
  @ ensures -1 <= \result <= 0;
*/
int read_test_instrumentation_channel(uint8_t div, uint8_t channel, uint32_t *val);

/*@ assigns \nothing;
  @ ensures \result < NVOTE_LOGIC;
*/
uint8_t get_test_actuation_unit(void);
/*$ spec get_test_actuation_unit();
    requires true;
    ensures return < NVOTE_LOGIC();
$*/

// NOTE: this is actually never used (only in `bottom.c`)
int is_actuation_unit_under_test(uint8_t id);

/* @ requires div < NVOTE_LOGIC;
  @ assigns core.test.test_actuation_unit_done[div];
  @ ensures core.test.test_actuation_unit_done[div] == v;
*/
void set_actuation_unit_test_complete(uint8_t div, int v);

/* @ requires id < NVOTE_LOGIC;
  @ assigns core.test.actuation_old_vote;
  @ ensures core.test.actuation_old_vote == v;
*/
void set_actuation_unit_test_input_vote(uint8_t id, int v);

/*@ requires id < NVOTE_LOGIC;
  @ assigns \nothing;
*/
int is_actuation_unit_test_complete(uint8_t id);
/*$ spec is_actuation_unit_test_complete(u8 id);
    requires id < NVOTE_LOGIC();
    ensures true;
$*/

/* @ requires dev < NDEV; DONE
  @ assigns core.test.test_device_result[dev]; TODO
  @ ensures core.test.test_device_result[dev] == result; TODO
*/
void set_actuate_test_result(uint8_t dev, uint8_t result);
/*$ spec set_actuate_test_result(u8 dev, u8 result);
    requires dev < NDEV();
    ensures true;
$*/

/* @ requires dev < NDEV; DONE
  @ assigns core.test.test_device_done[dev]; TODO
  @ ensures core.test.test_device_done[dev] == v; TODO
*/
void set_actuate_test_complete(uint8_t dev, int v);
/*$ spec set_actuate_test_complete(u8 dev, i32 v);
    requires dev < NDEV();
    ensures true;
$*/

/*@ requires dev < NDEV;
  @ assigns \nothing;
*/
int is_actuate_test_complete(uint8_t dev);
/*$ spec is_actuate_test_complete(u8 dev);
    requires dev < NDEV();
    ensures true;
$*/


////////////////////////////////////////////
// General Utilities                      //
////////////////////////////////////////////

/**
 * Return uptime in seconds
 * Platform specific
 */
uint32_t time_in_s(void);

/**
 * Update user display
 * Platform specific
 */
void update_display(void);

/**
 * Poll sensors for new values
 * Platform specific
 */
void update_sensors(void);

#endif // PLATFORM_H_
