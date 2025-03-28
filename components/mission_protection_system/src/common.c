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

#include <stddef.h>
#include <stdint.h>
#ifdef CN_ENV
#define div no_thanks
#include <stdlib.h>
#undef div
#else
#include <stdlib.h>
#endif

#include "platform.h"
#include "common.h"
#include "core.h"
#include "instrumentation.h"
#include "actuation_logic.h"
#include "sense_actuate.h"

#ifdef PLATFORM_HOST
#include <stdio.h>
#else
#include "printf.h"
#endif

#ifdef ENABLE_GPIO
#include "gpio_linux.h"
#endif

struct core_state core = {0};
struct instrumentation_state instrumentation[4];
struct actuation_logic actuation_logic[2];

// channel -> sensor # -> val
uint32_t sensors[2][2];
// channel -> sensor # -> demux output # -> val
uint32_t sensors_demux[2][2][2];

uint8_t trip_signals[NTRIP][4];
struct instrumentation_command inst_command_buf[4];

#ifdef CN_ENV
// workaround for file-local variable inst_command_buf
void acquire_inst_command_buf(void);
/*$ spec acquire_inst_command_buf();
  // @PropertyClass: P3-SOP
  // @PropertyClass: P10-SimpleLocks
  ensures
   take icb = Owned<struct instrumentation_command[4]>(&inst_command_buf);
$*/
void release_inst_command_buf(void);
/*$ spec release_inst_command_buf();
  // @PropertyClass: P3-SOP
  // @PropertyClass: P10-SimpleLocks
  requires
   take icb = Owned<struct instrumentation_command[4]>(&inst_command_buf);
$*/
#else
void acquire_inst_command_buf(void) {}
void release_inst_command_buf(void) {}
#endif
uint8_t actuator_state[NDEV];
uint8_t device_actuation_logic[2][NDEV];

//EI mode:
//  mode = 0 => no error
//  mode = 1 => error
//  mode = 2 => nondet error
uint8_t error_instrumentation_mode[NINSTR];
uint8_t error_instrumentation[NINSTR];
// ES ch mode:
//   mode = 0 => no error
//   mode = 1 => demux error (out 0)
//   mode = 2 => demux error (out 1)
//   mode = 3 => sensor error (error in both demux outs)
//   mode = 4 => nondet sensor error
//   mode = 5 => nondet demux error
uint8_t error_sensor_mode[2][2];
uint8_t error_sensor[2][2];
uint8_t error_sensor_demux[2][2][2];

int read_instrumentation_channel(uint8_t div, uint8_t channel, uint32_t *val) {
  MUTEX_LOCK(&mem_mutex);
  int sensor = div/2;
  int demux_out = div%2;
  /*$ extract Owned<uint32_t[2][2]>, (u64)channel; $*/
  /*$ extract Owned<uint32_t[2]>, (u64)sensor; $*/
  /*$ extract Owned<uint32_t>, (u64)demux_out; $*/
  *val = sensors_demux[channel][sensor][demux_out];
  MUTEX_UNLOCK(&mem_mutex);
  DEBUG_PRINTF(("<common.c> read_instrumentation_channel: div=%u,channel=%u,val=%u\n",div,channel,*val));
  return 0;
}

int get_instrumentation_value(uint8_t division, uint8_t ch, uint32_t *value) {
  MUTEX_LOCK(&mem_mutex);
  if (!error_instrumentation[division])
    *value = instrumentation[division].reading[ch];
  MUTEX_UNLOCK(&mem_mutex);
  DEBUG_PRINTF(("<common.c> get_instrumentation_value: error=%u, division=%u,ch=%u,val=%u\n",error_instrumentation[division], division,ch,*value));
  return 0;
}

int get_instrumentation_trip(uint8_t division, uint8_t ch, uint8_t *value) {
  MUTEX_LOCK(&mem_mutex);
  if (!error_instrumentation[division])
    *value = instrumentation[division].sensor_trip[ch];
  MUTEX_UNLOCK(&mem_mutex);
  DEBUG_PRINTF(("<common.c> get_instrumentation_trip: error=%u, division=%u,ch=%u,val=%u\n",error_instrumentation[division], division,ch,*value));
  return 0;
}

int get_instrumentation_mode(uint8_t division, uint8_t ch, uint8_t *value) {
  MUTEX_LOCK(&mem_mutex);
  if (!error_instrumentation[division])
    *value = instrumentation[division].mode[ch];
  MUTEX_UNLOCK(&mem_mutex);
  DEBUG_PRINTF(("<common.c> get_instrumentation_mode: error=%u, division=%u,ch=%u,val=%u\n",error_instrumentation[division], division,ch,*value));
  return 0;
}

int get_instrumentation_maintenance(uint8_t division, uint8_t *value) {
  MUTEX_LOCK(&mem_mutex);
  if (!error_instrumentation[division])
    *value = instrumentation[division].maintenance;
  MUTEX_UNLOCK(&mem_mutex);
  DEBUG_PRINTF(("<common.c> get_instrumentation_maintenance: error=%u, division=%u,val=%u\n",error_instrumentation[division],division,*value));
  return 0;
}

int get_actuation_state(uint8_t i, uint8_t device, uint8_t *value) {
  MUTEX_LOCK(&mem_mutex);
  /*$ extract Owned<uint8_t[2]>, (u64)i; $*/
  /*$ extract Owned<uint8_t>, (u64)device; $*/
#ifndef CN_ENV
  *value = device_actuation_logic[i][device];
#else
  // TODO this should be maintaned by an invariant on device_actuation_logic
  *value = !!device_actuation_logic[i][device];
#endif
  MUTEX_UNLOCK(&mem_mutex);
  DEBUG_PRINTF(("<common.c> get_actuation_state: i=%u,device=%u,val=%u\n",i,device,*value));
  return 0;
}

int read_instrumentation_trip_signals(uint8_t arr[3][4]) {
  DEBUG_PRINTF(("<common.c> read_instrumentation_trip_signals: ["));
  for (int i = 0; i < NTRIP; ++i) {
    DEBUG_PRINTF(("["));
    for (int div = 0; div < 4; ++div) {
      MUTEX_LOCK(&mem_mutex);
      arr[i][div] = trip_signals[i][div];
      DEBUG_PRINTF(("%u",trip_signals[i][div]));
      MUTEX_UNLOCK(&mem_mutex);
    }
    DEBUG_PRINTF(("],"));
  }
  DEBUG_PRINTF(("]\n"));
  return 0;
}

int reset_actuation_logic(uint8_t logic_no, uint8_t device_no, uint8_t reset_val) {
  MUTEX_LOCK(&mem_mutex);
  actuation_logic[logic_no].vote_actuate[device_no] = reset_val;
  MUTEX_UNLOCK(&mem_mutex);
  DEBUG_PRINTF(("<common.c> reset_actuation_logic: logic_no=%u,device=%u,reset_val=%u\n",logic_no,device_no,reset_val));
  return 0;
}

int set_output_actuation_logic(uint8_t logic_no, uint8_t device_no, uint8_t on) {
  ASSERT(logic_no < 2);
  ASSERT(device_no < 2);

  MUTEX_LOCK(&mem_mutex);

  /*$ extract Owned<uint8_t[3]>, (u64)logic_no; $*/
  /*$ extract Owned<uint8_t>, (u64)device_no; $*/
  device_actuation_logic[logic_no][device_no] = on;
  MUTEX_UNLOCK(&mem_mutex);
  DEBUG_PRINTF(("<common.c> set_output_actuation_logic: logic_no=%u,device=%u,on=%u\n",logic_no,device_no,on));
  return 0;
}

int set_output_instrumentation_trip(uint8_t div, uint8_t channel, uint8_t val) {
  MUTEX_LOCK(&mem_mutex);
  /*$ extract Owned<uint8_t>, (u64)div; $*/
  if (!error_instrumentation[div]) {
    /*$ extract Owned<uint8_t[4]>, (u64)channel; $*/
    /*$ extract Owned<uint8_t>, (u64)div; $*/
    trip_signals[channel][div] = val;
  }
  MUTEX_UNLOCK(&mem_mutex);
  DEBUG_PRINTF(("<common.c> set_output_instrumentation_trip: error=%u,div=%u,channel=%u,val=%u\n",error_instrumentation[div], div, channel, val));
  return 0;
}

int set_actuate_device(uint8_t device_no, uint8_t on)
{
  MUTEX_LOCK(&mem_mutex);
  /*$ extract Owned<uint8_t>, (u64)device_no; $*/
  actuator_state[device_no] = on;
  MUTEX_UNLOCK(&mem_mutex);
#ifdef ENABLE_GPIO
  gpio_set_value(device_no, on);
#endif
  DEBUG_PRINTF(("<common.c> set_actuate_device: dev %u, on %u\n",device_no, on));
  return 0;
}

// Implements: TA2-REQ-31
int read_instrumentation_command(uint8_t div,
                                 struct instrumentation_command *cmd) {
  acquire_inst_command_buf();
  DEBUG_PRINTF(("<common.c> read_instrumentation_command\n"));
  /*$ extract Owned<struct instrumentation_command>, (u64)div; $*/
  if ((div < 4) && (inst_command_buf[div].valid == 1)) {
    cmd->type = inst_command_buf[div].type;
    cmd->cmd = inst_command_buf[div].cmd;
    cmd->valid = 1;
    inst_command_buf[div].valid = 0;
    release_inst_command_buf();
    return 1;
  }
  release_inst_command_buf();
  return 0;
}

int send_instrumentation_command(uint8_t div,
                                 struct instrumentation_command *cmd) {
  DEBUG_PRINTF(("<common.c> send_instrumentation_command\n"));
  if (div < 4) {
    acquire_inst_command_buf();
    /*$ extract Owned<struct instrumentation_command>, (u64)div; $*/
    inst_command_buf[div].type = cmd->type;
    inst_command_buf[div].cmd = cmd->cmd;
    inst_command_buf[div].valid = 1;
    release_inst_command_buf();
    return 0;
  }
  return -1;
}

uint8_t is_test_running()
{
  MUTEX_LOCK(&mem_mutex);
  uint8_t ret = core.test.self_test_running;
  MUTEX_UNLOCK(&mem_mutex);
  DEBUG_PRINTF(("<common.c> is_test_running? %u\n",ret));
  return ret;
}

void set_test_running(int val)
{
  MUTEX_LOCK(&mem_mutex);
  core.test.self_test_running = val;
  MUTEX_UNLOCK(&mem_mutex);
  DEBUG_PRINTF(("<common.c> set_test_running: %i\n",core.test.self_test_running));
}

uint8_t get_test_device()
{
  DEBUG_PRINTF(("<common.c> get_test_device: %u\n",core.test.test_device));
  return core.test.test_device;
}

void get_test_instrumentation(uint8_t *id)
{
  /*$ extract Owned<uint8_t>, 0u64; $*/
  /*$ extract Block<uint8_t>, 0u64; $*/
  id[0] = core.test.test_instrumentation[0];
  /*$ extract Owned<uint8_t>, 1u64; $*/
  /*$ extract Block<uint8_t>, 1u64; $*/
  id[1] = core.test.test_instrumentation[1];
  DEBUG_PRINTF(("<common.c> get_test_instrumentation\n"));
}

int get_instrumentation_test_setpoints(uint8_t id, uint32_t *setpoints)
{
  setpoints[0] = core.test.test_setpoints[id][0];
  setpoints[1] = core.test.test_setpoints[id][1];
  setpoints[2] = core.test.test_setpoints[id][2];
  DEBUG_PRINTF(("<common.c> get_instrumentation_test_setpoints\n"));
  return 0;
}

void set_instrumentation_test_complete(uint8_t div, int v)
{
  MUTEX_LOCK(&mem_mutex);
  /*$ extract Owned<uint8_t>, (u64)div; $*/
  core.test.test_instrumentation_done[div] = v;
  MUTEX_UNLOCK(&mem_mutex);
  DEBUG_PRINTF(("<common.c> set_instrumentation_test_complete: div=%u,v=%i\n",div,v));
}

int is_instrumentation_test_complete(uint8_t id)
{
  MUTEX_LOCK(&mem_mutex);
  /*$ extract Owned<uint8_t>, (u64)id; $*/
  int ret = core.test.test_instrumentation_done[id];
  MUTEX_UNLOCK(&mem_mutex);
  DEBUG_PRINTF(("<common.c> is_instrumentation_test_complete: id=%u,ret=%i\n",id,ret));
  return ret;
}

int read_test_instrumentation_channel(uint8_t div, uint8_t channel, uint32_t *val)
{
  MUTEX_LOCK(&mem_mutex);
  /*$ extract Owned<uint32_t[2]>, (u64)div; $*/
  /*$ extract Owned<uint32_t>, (u64)channel; $*/
  *val = core.test.test_inputs[div][channel];
  MUTEX_UNLOCK(&mem_mutex);
  DEBUG_PRINTF(("<common.c> read_test_instrumentation_channel: div=%u,channel=%u,val=%u\n",div,channel,*val));
  return 0;
}

uint8_t get_test_actuation_unit()
{
  MUTEX_LOCK(&mem_mutex);
  uint8_t ret = core.test.test_actuation_unit;
  MUTEX_UNLOCK(&mem_mutex);
  DEBUG_PRINTF(("<common.c> get_test_actuation_unit: %u\n",ret));
  return ret;
}

void set_actuation_unit_test_complete(uint8_t div, int v)
{
  MUTEX_LOCK(&mem_mutex);
  /*$ extract Owned<uint8_t>, (u64)div; $*/
  core.test.test_actuation_unit_done[div] = v;
  MUTEX_UNLOCK(&mem_mutex);
  DEBUG_PRINTF(("<common.c> set_actuation_unit_test_complete: div %u, v=%i\n",div,v));
}

void set_actuation_unit_test_input_vote(uint8_t id, int v)
{
  MUTEX_LOCK(&mem_mutex);
  core.test.actuation_old_vote = v != 0;
  MUTEX_UNLOCK(&mem_mutex);
  DEBUG_PRINTF(("<common.c> set_actuation_unit_test_input_vote: id %u, v=%i\n",id,v));
}

int is_actuation_unit_test_complete(uint8_t id)
{
  MUTEX_LOCK(&mem_mutex);
  /*$ extract Owned<uint8_t>, (u64)id; $*/
  int ret = core.test.test_actuation_unit_done[id];
  MUTEX_UNLOCK(&mem_mutex);
  DEBUG_PRINTF(("<common.c> is_actuation_unit_test_complete: %i\n",ret));
  return ret;
}

void set_actuate_test_result(uint8_t dev, uint8_t result)
{
  MUTEX_LOCK(&mem_mutex);
  /*$ extract Owned<uint8_t>, (u64)dev; $*/
  core.test.test_device_result[dev] = result;
  MUTEX_UNLOCK(&mem_mutex);
  DEBUG_PRINTF(("<common.c> set_actuate_test_result: dev %u, result=%u\n",dev,result));
}

void set_actuate_test_complete(uint8_t dev, int v)
{
  MUTEX_LOCK(&mem_mutex);
  /*$ extract Owned<uint8_t>, (u64)dev; $*/
  core.test.test_device_done[dev] = v;
  MUTEX_UNLOCK(&mem_mutex);
  DEBUG_PRINTF(("<common.c> set_actuate_test_complete: dev %u, v=%i\n",dev,v));
}

int is_actuate_test_complete(uint8_t dev)
{
  MUTEX_LOCK(&mem_mutex);
  /*$ extract Owned<uint8_t>, (u64)dev; $*/
  int ret = core.test.test_device_done[dev];
  MUTEX_UNLOCK(&mem_mutex);
  DEBUG_PRINTF(("<common.c> is_actuate_test_complete: %i\n",ret));
  return ret;
}

void zero_u8_arr(uint8_t *a, unsigned int n)
{
  for (unsigned int j = 0; j < n; j++)
  /*$ inv take al = each(u64 k; k < (u64)j) { Owned<uint8_t>( array_shift<uint8_t>(a, k)) };
    take ar = each(u64 l; (u64)j <= l && l < (u64)n) { Block<uint8_t>( array_shift<uint8_t>(a, l)) };
    {a} unchanged; {n} unchanged;
    j <= (u32)n;
    $*/
  {
    /*$ extract Block<uint8_t>, (u64)j;$*/
    /*$ extract Owned<uint8_t>, (u64)j;$*/
    a[j] = 0;
  }
}

void zero_u32_arr(uint32_t *a, unsigned int n)
{
  for (unsigned int j = 0; j < n; j++)
  /*$ inv take al = each(u64 k; k < (u64)j) { Owned<uint32_t>( array_shift<uint32_t>(a, k)) };
    take ar = each(u64 i; (u64)j <= i && i < (u64)n) { Block<uint32_t>( array_shift<uint32_t>(a, i)) };
    {a} unchanged; {n} unchanged;
    j <= (u32)n;
    $*/
  {
    /*$ extract Block<uint32_t>, (u64)j;$*/
    /*$ extract Owned<uint32_t>, (u64)j;$*/
    a[j] = 0;
  }
}
