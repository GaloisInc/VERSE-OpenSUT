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

#include "core.h"
#include "platform.h"
#include "actuate.h"
#include "mps.h"
#include <string.h>

#ifdef PLATFORM_HOST
#include <stdio.h>
#else
#include "printf.h"
#endif
// TODO move elsewhere. Probably an include that's always included after printf.h
/*$ spec snprintf(pointer p, size_t n, pointer f);
  requires true;
  ensures true;
$*/

#ifdef CN_ENV
#define actuate_devices_generated_C actuate_devices
#endif

#define INST_OFFSET 0
#define ACT_OFFSET 5
char INSTR_LINE_FMT[] = "#I %d (%c): T[%10d %c %d] P[%10d %c %d] S[%10d %c %d]";
char ACT_LINE_FMT[] = "#A %d [%d %d]";

const char self_test_running[]     = "SELF TEST:     RUNNING";
const char self_test_not_running[] = "SELF TEST: NOT RUNNING";
const char pass[] = "LAST TEST: PASS";
const char fail[] = "LAST TEST: FAIL";

char sensor_warning[] = "WARNING: LARGE SENSOR DIFFERENTIAL";
char sensor_ok[] = "SENSORS OK";

#ifdef ENABLE_SELF_TEST
struct testcase {
  uint32_t input[4][2];
  uint32_t setpoints[4][3];
  uint8_t instrumentation[2];
  uint8_t actuation_unit;
  uint8_t device;
  uint8_t expect;
} tests[] = {
// Test data generated from Cryptol MPS::SelfTestOracleHalf
#include "self_test_data/tests.inc.c"
};
#endif

char mode_char(uint8_t mode) {
  switch (mode) {
  case BYPASS:
    return 'B';
  case OPERATE:
    return 'O';
  case TRIP:
    return 'T';
  default:
    return '?';
  }
}

char maint_char(uint8_t mode) {
  if (mode)
    return 'M';
  else
    return '_';
}

int update_ui_instr(struct ui_values *ui)
/*$
  // @PropertyClass: P3-SOP
  // @PropertyClass: P2-LIV
    accesses error_instrumentation;
    requires take uii = Owned<struct ui_values>(ui);
    ensures take uio = Owned<struct ui_values>(ui);
$*/
{
  int err = 0;
  int sensor_differential = 0;

#ifndef WAR_CN_254
  char line[256];
#else
  char line[256] = {0};
#endif

  for (uint8_t i = 0; i < NDIVISIONS; ++i)
    /*$ inv i >= 0u8;
        i <= NDIVISIONS();
        take uiinv = Owned<struct ui_values>(ui);
        {ui} unchanged;
    $*/
  {
    for (uint8_t ch = 0; ch < NTRIP; ++ch)
      /*$ inv i >= 0u8;
          i < NDIVISIONS();
          ch >= 0u8;
          ch <= NTRIP();
          take uiinv2 = Owned<struct ui_values>(ui);
          {ui} unchanged;
          $*/
    {
      /*$ extract Owned<uint32_t[3]>, (u64)i; $*/
      /*$ extract Owned<uint32_t>, (u64)ch; $*/
      if ((err = get_instrumentation_value(i, ch, &ui->values[i][ch])) < 0)
        return err;
      /*$ extract Owned<uint8_t[3]>, (u64)i; $*/
      /*$ extract Owned<uint8_t>, (u64)ch; $*/
      if ((err = get_instrumentation_mode(i, ch, &ui->bypass[i][ch])) < 0)
        return err;
      if ((err = get_instrumentation_trip(i, ch, &ui->trip[i][ch])) < 0)
        return err;
    }
    /*$ extract Owned<uint8_t>, (u64)i; $*/
    if ((err = get_instrumentation_maintenance(i, &ui->maintenance[i])) < 0)
      return err;

    /*$ extract Owned<uint32_t[3]>, (u64)i; $*/
    /*$ extract Owned<uint32_t>, (u64)P(); $*/
    /*$ extract Owned<uint32_t>, (u64)S(); $*/
    /*$ extract Owned<uint32_t>, (u64)T(); $*/
    /*$ extract Owned<uint8_t[3]>, (u64)i; $*/
    /*$ extract Owned<uint8_t>, (u64)P(); $*/
    /*$ extract Owned<uint8_t>, (u64)S(); $*/
    /*$ extract Owned<uint8_t>, (u64)T(); $*/

    snprintf(line, sizeof(line), INSTR_LINE_FMT, INST_OFFSET + i,
             maint_char(ui->maintenance[i]), ui->values[i][T],
             mode_char(ui->bypass[i][T]), 0 != ui->trip[i][T], ui->values[i][P],
             mode_char(ui->bypass[i][P]), 0 != ui->trip[i][P], ui->values[i][S],
             mode_char(ui->bypass[i][S]), 0 != ui->trip[i][S]);

    set_display_line(ui, i, line, sizeof(line));
  }

  // Flag any sensor differences that exceed thresholds
  for (uint8_t i = 0; i < NDIVISIONS; ++i)
    /*$ inv i >= 0u8;
        i <= NDIVISIONS();
        take uiinv = Owned<struct ui_values>(ui);
        {ui} unchanged;
    $*/
  {

    /*$ extract Owned<uint8_t>, (u64)i; $*/
    if (ui->maintenance[i])
      continue;

    for (uint8_t j = 0; j < NDIVISIONS; ++j)
      /*$ inv i >= 0u8;
          i < NDIVISIONS();
          j >= 0u8;
          j <= NDIVISIONS();
          take uiinv2 = Owned<struct ui_values>(ui);
          {ui} unchanged;
      $*/
    {
      /*$ extract Owned<uint8_t>, (u64)j; $*/
      if (ui->maintenance[j])
        continue;

      /*$ extract Owned<uint32_t[3]>, (u64)i; $*/
      /*$ extract Owned<uint32_t[3]>, (u64)j; $*/
      /*$ split_case(i==j); $*/
      /*$ extract Owned<uint32_t>, (u64)P(); $*/
      /*$ extract Owned<uint32_t>, (u64)S(); $*/
      /*$ extract Owned<uint32_t>, (u64)T(); $*/
      sensor_differential |=
        (ui->values[i][T] > ui->values[j][T] &&
         ui->values[i][T] - ui->values[j][T] > T_THRESHOLD);
      sensor_differential |=
        (ui->values[i][P] > ui->values[j][P] &&
         ui->values[i][P] - ui->values[j][P] > P_THRESHOLD);
    }
  }

  if (sensor_differential)
    set_display_line(ui, 14, sensor_warning, sizeof(sensor_warning));
  else
    set_display_line(ui, 14, sensor_ok, sizeof(sensor_ok));

  return err;
}

int update_ui_actuation(struct ui_values *ui)
/*$
  // @PropertyClass: P2-LIV
  // @PropertyClass: P3-SOP
    accesses ACT_LINE_FMT;
    requires take uii = Owned<struct ui_values>(ui);
    ensures take uio = Owned<struct ui_values>(ui);
$*/
{
  int err = 0;
  for (int i = 0; i < 2; ++i)
  /*$ inv i >=0i32; i <= 2i32;
    {ui} unchanged;
    {&ACT_LINE_FMT} unchanged;
      take ui_l1 = Owned<struct ui_values>(ui);
    //{(*ui).values} unchanged;
  $*/
  {
#ifndef WAR_CN_254
    char line[256];
#else
    char line[256] = {0};
#endif
    for (int d = 0; d < 2; ++d)
    /*$ inv d >=0i32; d <= 2i32;
      i >=0i32; i < 2i32;
      //take l = each (u64 j; j >= 0u64 && j < 2u64) {Owned<char>(array_shift<char>(&line, j))};
      {&line} unchanged;
      take ui_l2 = Owned<struct ui_values>(ui);
    {ui} unchanged;
    {&ACT_LINE_FMT} unchanged;
    //{(*ui).values} unchanged;
    $*/
    {
      uint8_t val;
      err |= get_actuation_state(i, d, &val);
      /*$ extract Owned<uint8_t[2]>, (u64) i; $*/
      /*$ extract Owned<uint8_t>, (u64) d; $*/
      ui->actuators[i][d] = val;
    }
      /*$ extract Owned<uint8_t[2]>, (u64) i; $*/
      /*$ extract Owned<uint8_t>, 0u64; $*/
      /*$ extract Owned<uint8_t>, 1u64; $*/
    snprintf(line, sizeof(line), ACT_LINE_FMT, i, ui->actuators[i][0],
             ui->actuators[i][1]);
    set_display_line(ui, ACT_OFFSET + i, line, sizeof(line));
  }

  return err;
}

int update_ui(struct ui_values *ui)
/*$
  // @PropertyClass: P3-SOP
    accesses error_instrumentation;
    accesses ACT_LINE_FMT;
    requires take uii = Owned<struct ui_values>(ui);
    ensures take uio = Owned<struct ui_values>(ui);
$*/
{
  DEBUG_PRINTF(("<core.c> update_ui\n"));
  int err = 0;
  err |= update_ui_instr(ui);
  err |= update_ui_actuation(ui);

  return err;
}

int set_display_line(struct ui_values *ui, uint8_t line_number, char *display, uint32_t size) {
  memset(ui->display[line_number], ' ', LINELENGTH);
  strncpy(ui->display[line_number], (const char*)display, LINELENGTH);
  return 0;
}

#ifdef ENABLE_SELF_TEST
int end_test(struct test_state *test, struct ui_values *ui) {
    static int cnt = 0;
    int passed =
         test->test_device_result[test->test_device]
      == (test->self_test_expect || test->actuation_old_vote);
    test->failed = !passed;
    DEBUG_PRINTF(("<core.c> end_test #%d: test->test_device_result[%u]=0x%X\n", cnt, test->test_device, test->test_device_result[test->test_device]));
    DEBUG_PRINTF(("<core.c> end_test #%d: (test->self_test_expect || test->actuation_old_vote)=0x%X\n", cnt, (test->self_test_expect || test->actuation_old_vote)));

    // Reset state
    set_test_running(0);

    if (passed) {
      set_display_line(ui, 16, (char*)pass, 0);
      test->test++;
      if (test->test >= sizeof(tests)/sizeof(struct testcase)) {
        test->test = 0;
        test->test_timer_start = time_in_s();
      }
    } else {
      set_display_line(ui, 16, (char*)fail, 0);
      set_display_line(ui, 20, (char*)"A TEST FAILED", 0);
    }
    DEBUG_PRINTF(("<core.c> end_test #%d: Passed: %d\n", cnt, passed));
    cnt++;
    return passed;
}

int components_ready() {
  return !is_instrumentation_test_complete(0)
         && !is_instrumentation_test_complete(1)
         && !is_instrumentation_test_complete(2)
         && !is_instrumentation_test_complete(3)
         && !is_actuation_unit_test_complete(0)
         && !is_actuation_unit_test_complete(1)
         && !is_actuate_test_complete(0)
         && !is_actuate_test_complete(1);
}

int self_test_timer_expired(struct test_state *test) {
  uint32_t t    = time_in_s();
  uint32_t diff = t - test->test_timer_start;
  return SELF_TEST_PERIOD_SEC < diff;
}

int should_start_self_test(struct test_state *test) {
  int retval = (!is_test_running()) && (self_test_timer_expired(test) || (test->test != 0));
  return retval;
}

int test_step(struct test_state *test, struct ui_values *ui) {
  DEBUG_PRINTF(("<core.c> test_step: Has test failed? %u\n",test->failed));
  int err = 0;

  if(!test->failed && should_start_self_test(test)) {
    if (components_ready())
    {
      struct testcase *next = &tests[test->test];
      test->self_test_expect = next->expect;
      test->test_device = next->device;
      test->test_actuation_unit = next->actuation_unit;
      DEBUG_PRINTF(("<core.c> test_step: starting new test. test->self_test_expect=%u,test->test_device=%u, test->test_actuation_unit=%u,\n",
        test->self_test_expect,test->test_device,test->test_actuation_unit));
      memcpy(test->test_instrumentation, next->instrumentation, 2);
      memcpy(test->test_inputs, next->input, 2*4*sizeof(uint32_t));
      memcpy(test->test_setpoints, next->setpoints, 3*4*sizeof(uint32_t));

      set_test_running(1);
      set_display_line(ui, 15, (char *)self_test_running, 0);
    }
  } else if (is_test_running() && test->test_device_done[test->test_device]) {
    DEBUG_PRINTF(("<core.c> test_step: Ending test\n"));
    int passed = end_test(test, ui);
    if(!passed) err = -1;
  } else if (!is_test_running()) {
    DEBUG_PRINTF(("<core.c> test_step:Continuing test\n"));
    set_display_line(ui, 15, (char *)self_test_not_running, 0);
  } else {
    DEBUG_PRINTF(("<core.c> test_step:Catchall\n"));
  }

  return err;
}
#endif

void core_init(struct core_state *c) {
  c->test.test_timer_start = time_in_s();
  c->test.failed = 0;
}

int core_step(struct core_state *c) {
  int err = 0;
  struct mps_command mps;
#ifndef ENABLE_SELF_TEST
  time_in_s();
#endif

  if (!c->error) {
    // Actuate devices if necessary
    int retval = actuate_devices_generated_C();
    DEBUG_PRINTF(("<core.c> actuate_devices_generated_C: 0x%X\n", retval));
  }

  // Let's allow command processing even if an error is detected.
  // In a real system, we would probably want to disconnect the device
  // and perform maintenance.
  int read_cmd = read_mps_command(&mps);
  if (read_cmd < 0) {
    err |= -read_cmd;
  } else if (read_cmd > 0) {
    switch (mps.type) {
    case INSTRUMENTATION_COMMAND:
      err |= send_instrumentation_command(mps.instrumentation_division,
                                          &(mps.cmd.instrumentation));
      break;

    case ACTUATION_COMMAND:
      err |= send_actuation_command(0, &mps.cmd.act);
      err |= send_actuation_command(1, &mps.cmd.act);
      break;

    default:
      break;
    }
  }

#ifdef ENABLE_SELF_TEST
  err |= test_step(&c->test, &c->ui);
#endif
  err |= update_ui(&c->ui);

  c->error = err;
  return err;
}
