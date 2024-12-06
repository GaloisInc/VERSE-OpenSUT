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
#include "core.h"
#include "instrumentation.h"
#include "actuation_logic.h"
#include "sense_actuate.h"
#include "platform.h"

#include <poll.h>
#include <fcntl.h>
#include <stdio.h>
#include <termios.h>
#include <unistd.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/select.h>
#include <time.h>
/*$ spec fileno(pointer stream);
    requires take si = Owned<FILE>(stream);
    ensures take so = Owned<FILE>(stream);
$*/
/*$ spec clock_gettime(i32 clock_id, pointer tp);
    requires take tpi = Block<struct timespec>(tp);
    ensures take tpo = Owned<struct timespec>(tp);
$*/
/*$ spec rand();
    requires true;
    ensures true;
$*/
/*$ spec exit(i32 status);
    requires true;
    ensures true;
$*/
/*$ spec sprintf(pointer a, pointer b);
    requires true;
    ensures true;
$*/

extern struct instrumentation_state instrumentation[4];
struct actuation_command *act_command_buf[2];

#define min(_a, _b) ((_a) < (_b) ? (_a) : (_b))
#define max(_a, _b) ((_a) > (_b) ? (_a) : (_b))

#include <pthread.h>
pthread_mutex_t display_mutex = PTHREAD_MUTEX_INITIALIZER;
pthread_mutex_t mem_mutex = PTHREAD_MUTEX_INITIALIZER;

// Like `exit(status)`, but cleanly shuts down threads if needed.
void clean_exit(int status) __attribute__((noreturn));

#ifndef T0
#define T0 200
#endif

#ifndef P0
#define P0 1152600
#endif

// Bias to simulated sensor readings in degrees F
#ifndef T_BIAS
#define T_BIAS 0
#endif

// Bias to simulated sensor readings in 10^-5 lb/in2
#ifndef P_BIAS
#define P_BIAS 0
#endif

#ifndef SENSOR_UPDATE_MS
#define SENSOR_UPDATE_MS 500
#endif

int clear_screen()
  // problem: need to specify that stdin owns its pointee and is valid
/*$ accesses __stdin;
$*/
{
  return (isatty(fileno(stdin)) && (NULL == getenv("MPS_NOCLEAR")));
}

void update_display()
#if !WAR_CN_399
  /*$ accesses __stdin; $*/
#else
  /*$ trusted; $*/
#endif
{
  if (clear_screen()) {
    printf("\e[s\e[1;1H");//\e[2J");
  }
  for (int line = 0; line < NLINES; ++line) {
    printf("\e[0K");
    printf("%s%s", core.ui.display[line], line == NLINES-1 ? "" : "\n");
  }
  if (clear_screen()) {
    printf("\e[u");
  }
}

// A copy of the `argv` that was passed to main.  This is used to implement the
// reset (`R`) command inside `read_mps_command`.
static char** main_argv = NULL;

int read_mps_command(struct mps_command *cmd) {
  int ok = 0;
  uint8_t device, on, div, ch, mode, sensor;
  uint32_t val;
  char *line = NULL;
  size_t linecap = 0;
  ssize_t linelen;

  /* if (isatty(fileno(stdin))) { */
  /*   set_display_line(&ui, 9, (char *)"> ", 0); */
  /* } */
  struct pollfd fds;
  fds.fd = STDIN_FILENO;
  fds.events = POLLIN;
  fds.revents = POLLIN;
  if(poll(&fds, 1, 100) < 1) {
    return 0;
  }
  linelen = getline(&line, &linecap, stdin);

  if (linelen == EOF)
    clean_exit(0);

  if (linelen < 0)
    return 0;

  MUTEX_LOCK(&display_mutex);

  if (clear_screen()) {
    printf("\e[%d;1H\e[2K> ", NLINES+1);
  }

  MUTEX_UNLOCK(&display_mutex);

  if (2 == (ok = sscanf(line, "A %hhd %hhd", &device, &on))) {
    cmd->type = ACTUATION_COMMAND;
    cmd->cmd.act.device = device;
    cmd->cmd.act.on = on;
    DEBUG_PRINTF(("<main.c> read_mps_command ACTUATION_COMMAND dev=%u on=%u\n",
                  cmd->cmd.act.device, cmd->cmd.act.on));
    ok = 1;
  } else if (2 == (ok = sscanf(line, "M %hhd %hhd", &div, &on))) {
    cmd->type = INSTRUMENTATION_COMMAND;
    cmd->instrumentation_division = div;
    cmd->cmd.instrumentation.type = SET_MAINTENANCE;
    cmd->cmd.instrumentation.cmd.maintenance.on = on;
    DEBUG_PRINTF(("<main.c> read_mps_command INSTRUMENTATION_COMMAND MAINTENANCE div=%u on=%u, type=%u\n",
                  cmd->instrumentation_division,
                  cmd->cmd.instrumentation.cmd.maintenance.on,
                  cmd->cmd.instrumentation.type));
    ASSERT(on == 0 || on == 1);
    ok = 1;
  } else if (3 == (ok = sscanf(line, "B %hhd %hhd %hhd", &div, &ch, &mode))) {
    cmd->type = INSTRUMENTATION_COMMAND;
    cmd->instrumentation_division = div;
    cmd->cmd.instrumentation.type = SET_MODE;
    cmd->cmd.instrumentation.cmd.mode.channel = ch;
    cmd->cmd.instrumentation.cmd.mode.mode_val = mode;
    DEBUG_PRINTF(("<main.c> read_mps_command INSTRUMENTATION_COMMAND MODE div=%u channel=%u mode=%u type=%u\n",
                  cmd->instrumentation_division,
                  cmd->cmd.instrumentation.cmd.mode.channel,
                  cmd->cmd.instrumentation.cmd.mode.mode_val,
                  cmd->cmd.instrumentation.type));
    ok = 1;
  } else if (3 == (ok = sscanf(line, "S %hhd %hhd %d", &div, &ch, &val))) {
    cmd->type = INSTRUMENTATION_COMMAND;
    cmd->instrumentation_division = div;
    cmd->cmd.instrumentation.type = SET_SETPOINT;
    cmd->cmd.instrumentation.cmd.setpoint.channel = ch;
    cmd->cmd.instrumentation.cmd.setpoint.val = val;
    DEBUG_PRINTF(("<main.c> read_mps_command INSTRUMENTATION_COMMAND SETPOINT div=%u channel=%u val=%u\n",
                  cmd->instrumentation_division,
                  cmd->cmd.instrumentation.cmd.setpoint.channel,
                  cmd->cmd.instrumentation.cmd.setpoint.val));
    ok = 1;
#ifndef SIMULATE_SENSORS
  } else if (3 == (ok = sscanf(line, "V %hhd %hhd %d", &sensor, &ch, &val))) {
    if (sensor < 2 && ch < 2)
      sensors[ch][sensor] = val;
    DEBUG_PRINTF(("<main.c> read_mps_command UPDATE SENSORS sensor=%d, ch=%d, val=%d\n",
          sensor,ch,val));
#endif
  } else if (line[0] == 'Q') {
    printf("<main.c> read_mps_command QUIT\n");
    clean_exit(0);
  } else if (line[0] == 'R') {
    printf("<main.c> read_mps_command RESET\n");
    // Re-exec the MPS binary with the same arguments and environment.  This
    // has the effect of resetting the entire MPS to its initial state.
    execv("/proc/self/exe", main_argv);
  } else if (line[0] == 'D') {
    DEBUG_PRINTF(("<main.c> read_mps_command UPDATE DISPLAY\n"));
    update_display();
  } else if (3 == (ok = sscanf(line, "ES %hhd %hhd %hhd", &sensor, &ch, &mode))) {
    error_sensor_mode[ch][sensor] = mode;
    DEBUG_PRINTF(("<main.c> read_mps_command ERROR SENSOR sensor=%d, ch=%d, mode=%d\n",
          sensor,ch,mode));
  } else if (2 == (ok = sscanf(line, "EI %hhd %hhd", &div, &mode))) {
    error_instrumentation_mode[div] = mode;
    DEBUG_PRINTF(("<main.c> read_mps_command ERROR INSTRUMENTATION div=%d, mode=%d\n",
          div,mode));
  }

  if (line)
    free(line);

  return ok;
}

void update_instrumentation_errors(void)
/*$ accesses error_instrumentation_mode;
   accesses error_instrumentation;
$*/
{
  for (int i = 0; i < NINSTR; ++i)
    /*$ inv i >= 0i32; i <= (i32) NINSTR(); $*/
  {
    /*$ extract Owned<uint8_t>, (u64)i; $*/
    if(error_instrumentation_mode[i] == 2) {
      error_instrumentation[i] |= rand() % 2;
    } else {
      error_instrumentation[i] = error_instrumentation_mode[i];
    }
  }
}

// CN #357 is blocking this, otherwise should be simple
void update_sensor_errors(void)
/*$
    accesses error_sensor;
    accesses error_sensor_mode;
    accesses error_sensor_demux;
$*/
{
  for (int c = 0; c < 2; ++c)
    /*$ inv c >= 0i32; c <= 2i32;
      {error_sensor_mode} unchanged;
      {error_sensor_demux} unchanged;
     $*/
  {
    for (int s = 0; s < 2; ++s)
    /*$ inv s >= 0i32; s <= 2i32;
        c < 2i32;
        c >= 0i32;
        {&c} unchanged;
      {error_sensor_mode} unchanged;
      {error_sensor_demux} unchanged;
     $*/
    {
      /*$ extract Owned<uint8_t[2]>, (u64)c; $*/
      /*$ extract Owned<uint8_t>, (u64)s; $*/

          /*$ extract Owned<uint8_t[2][2]>, (u64)c; $*/
          /*$ extract Owned<uint8_t[2]>, (u64)s; $*/
          /*$ extract Owned<uint8_t>, 0u64; $*/
          /*$ extract Owned<uint8_t>, 1u64; $*/
          /*$ split_case(c==s); $*/
          /*$ split_case(s==0i32); $*/
      switch (error_sensor_mode[c][s]) {
        case 0:
          error_sensor[c][s] = 0;

          error_sensor_demux[c][s][0] = 0;
          error_sensor_demux[c][s][1] = 0;
          break;
        case 1:
          error_sensor[c][s] = 0;
          error_sensor_demux[c][s][0] = 1;
          error_sensor_demux[c][s][1] = 0;
          break;
        case 2:
          error_sensor[c][s] = 0;
          error_sensor_demux[c][s][0] = 0;
          error_sensor_demux[c][s][1] = 1;
          break;
        case 3:
          error_sensor[c][s] = 1;
          error_sensor_demux[c][s][0] = 0;
          error_sensor_demux[c][s][1] = 0;
          break;
        case 4:
        {
          int fail = rand() % 2;
          error_sensor[c][s] |= fail;
          error_sensor_demux[c][s][0] = 0;
          error_sensor_demux[c][s][1] = 0;
        }
        break;
        case 5:
        {
          error_sensor[c][s] = 0;
          error_sensor_demux[c][s][0] |= (rand() % 2);
          error_sensor_demux[c][s][1] |= (rand() % 2);
        }
        break;
        default:
          ASSERT("Invalid sensor fail mode" && 0);
      }
    }
  }
}

int update_sensor_simulation(void)
#if !WAR_CN_399
  /*$
    accesses last_update;
    accesses initialized;
    accesses last;
    accesses sensors;
    $*/
#else
/*$ trusted; $*/
#endif
{
  static int initialized = 0;
  static uint32_t last_update = 0;
  static uint32_t last[2][2] = {0};

  struct timespec tp;
  clock_gettime(CLOCK_REALTIME, &tp);
  uint32_t t0 = last_update;
  uint32_t t = tp.tv_sec*1000 + tp.tv_nsec/1000000;

  if (!initialized) {
    last_update = t;
    /*$ extract Owned<uint32_t[2]>, 0u64; $*/
    /*$ extract Owned<uint32_t>, (u64)T(); $*/
    last[0][T] = T0;
    /*$ extract Owned<uint32_t[2]>, 1u64; $*/
    ///*$ extract Owned<uint32_t>, (u64)T(); $*/
    last[1][T] = T0;
    /*$ extract Owned<uint32_t>, (u64)P(); $*/
    last[0][P] = P0;
    last[1][P] = P0;
    initialized = 1;
  } else if (t - t0 > SENSOR_UPDATE_MS) {
    for (int s = 0; s < 2; ++s)
      /*$ inv 0i32 <= s; s <= 2i32;
          $*/
    {
      /*$ extract Owned<uint32_t[2]>, (u64)s; $*/
      /*$ extract Owned<uint32_t>, (u64)T(); $*/
      last[s][T] += (rand() % 7) - 3 + T_BIAS;
      // Don't stray too far from our steam table
      last[s][T] = min(last[s][T], 300);
      last[s][T] = max(last[s][T], 25);

      /*$ extract Owned<uint32_t>, (u64)P(); $*/
      last[s][P] += (rand() % 7) - 3 + P_BIAS;
      // Don't stray too far from our steam table
      last[s][P] = min(last[s][P], 5775200);
      last[s][P] = max(last[s][P], 8000);
    }
    last_update = t;
  }
  /*$ extract Owned<uint32_t[2]>, (u64)T(); $*/
  /*$ extract Owned<uint32_t>, 0u64; $*/
  /*$ extract Owned<uint32_t>, 1u64; $*/
  ///*$ extract Owned<uint32_t[2]>, 0u64; $*/
  ///*$ extract Owned<uint32_t>, (u64)T(); $*/
  sensors[T][0] = last[T][0];
  sensors[T][1] = last[T][1];
  /*$ extract Owned<uint32_t[2]>, (u64)P(); $*/
  sensors[P][0] = last[P][0];
  sensors[P][1] = last[P][1];

  return 0;
}

// CN #357 again
void update_sensors(void)
  /*$ accesses error_sensor;
accesses error_sensor_mode;
accesses error_sensor_demux;
accesses sensors_demux;
accesses sensors;
    $*/
{
  update_sensor_errors();
#ifdef SIMULATE_SENSORS
  update_sensor_simulation();
#endif
  for (int c = 0; c < 2; ++c)
    /*$ inv c >= 0i32; c <= 2i32; $*/
  {
    for (int s = 0; s < 2; ++s)
    /*$ inv s >= 0i32; s <= 2i32;
            c >= 0i32; c < 2i32;
      $*/
    {
      /*$ extract Owned<uint8_t[2]>, (u64)c; $*/
      /*$ extract Owned<uint8_t>, (u64)s; $*/
      if (error_sensor[c][s]) {
        sensors[c][s] = rand();
      }

      MUTEX_LOCK(&mem_mutex);

      /*$ extract Owned<uint32_t[2][2]>, (u64)c; $*/
      /*$ extract Owned<uint32_t[2]>, (u64)s; $*/
      /*$ extract Owned<uint32_t>, 0u64; $*/
      /*$ split_case(c==s); $*/
      /*$ split_case(s==0i32); $*/
      sensors_demux[c][s][0] = sensors[c][s];
      MUTEX_UNLOCK(&mem_mutex);

      MUTEX_LOCK(&mem_mutex);
      sensors_demux[c][s][1] = sensors[c][s];
      MUTEX_UNLOCK(&mem_mutex);

      for (int d = 0; d < 2; ++d) {
        if(error_sensor_demux[c][s][d]) {
          MUTEX_LOCK(&mem_mutex);
          sensors_demux[c][s][d] = rand();
          MUTEX_UNLOCK(&mem_mutex);
        }
      }
    }
  }
}

int read_actuation_command(uint8_t id, struct actuation_command *cmd)
///*$ accesses act_command_buf; $*/
// TODO not possible to specify this because the spec needs to be in a header
// file and the body is here and act_command_buf is declared in this file,
// inaccessible to the header file. Might be working as intended
{
  /*$ extract Block<struct actuation_command *>, (u64)id; $*/
  struct actuation_command *c = act_command_buf[id];
  if (c) {
    cmd->device = c->device;
    cmd->on = c->on;
    free(c);
    act_command_buf[id] = NULL;
    return 1;
  }
  return 0;
}

int send_actuation_command(uint8_t id, struct actuation_command *cmd) {
  if (id < 2) {
    act_command_buf[id] = (struct actuation_command *)malloc(sizeof(*act_command_buf[id]));
    act_command_buf[id]->device = cmd->device;
    act_command_buf[id]->on = cmd->on;
    return 0;
  }
  return -1;
}

// Whether the sense_actuate threads should continue running.  The main thread
// sets this to 0 when it wants the sense_actuate threads to shut down.
static _Atomic int running = 1;
#ifdef USE_PTHREADS
// Number of threads started successfully.
static int threads_started = 0;
static pthread_t sense_actuate_0_thread = { 0 };
static pthread_t sense_actuate_1_thread = { 0 };
#endif

void* start0(void *arg) {
  while (running) {
    sense_actuate_step_0(&instrumentation[0], &actuation_logic[0]);
    usleep(100);
  }
  return NULL;
}
void* start1(void *arg) {
  while (running) {
    sense_actuate_step_1(&instrumentation[2], &actuation_logic[1]);
    usleep(100);
  }
  return NULL;
}

// TODO ensure names match gcc builtins
int sadd_overflow (int a, int b, int *res);
/*$ spec sadd_overflow(i32 a, i32 b, pointer res);
    requires take x = Block<int>(res);
    ensures take out = Owned<int>(res);
      (return == (1i32)) || (out == (a + b));
$*/
int smul_overflow (int a, int b, int *res);
/*$ spec smul_overflow(i32 a, i32 b, pointer res);
    requires take x = Block<int>(res);
    ensures take out = Owned<int>(res);
      (return == (1i32)) || (out == (a * b));
$*/
int ssub_overflow (int a, int b, int *res);
/*$ spec ssub_overflow(i32 a, i32 b, pointer res);
    requires take x = Block<int>(res);
    ensures take out = Owned<int>(res);
      (return == (1i32)) || (out == (a - b));
$*/
int dadd_overflow (int64_t a, int64_t b, int64_t *res);
/*$ spec dadd_overflow(i64 a, i64 b, pointer res);
    requires take x = Block<int64_t>(res);
    ensures take out = Owned<int64_t>(res);
      (return == (1i32)) || (out == (a + b));
$*/
int dmul_overflow (int64_t a, int64_t b, int64_t *res);
/*$ spec dmul_overflow(i64 a, i64 b, pointer res);
    requires take x = Block<int64_t>(res);
    ensures take out = Owned<int64_t>(res);
      (return == (1i32)) || (out == (a * b));
$*/
int dsub_overflow (int64_t a, int64_t b, int64_t *res);
/*$ spec dsub_overflow(i64 a, i64 b, pointer res);
    requires take x = Block<int64_t>(res);
    ensures take out = Owned<int64_t>(res);
      (return == (1i32)) || (out == (a - b));
$*/
uint32_t time_in_s()
{
  static time_t start_time = 0;
  struct timespec tp;
  clock_gettime(CLOCK_REALTIME, &tp);
  if (start_time == 0) {
    start_time = tp.tv_sec;
  }
  time_t total = tp.tv_sec - start_time;
  char line[256];
  sprintf(line, "Uptime: [%u]s\n",(uint32_t)total);
  set_display_line(&core.ui, 9, line, 0);
  return (uint32_t)total;
}

// TODO core_state_ok({0}) must be true

// VERSE-Toolchain#107 is the blocker here

int main(int argc, char **argv)
/*$
  requires
    take ci = Owned<struct core_state>(&core);
    core_state_ok(ci);
  //requires take ii = each(u64 j; j < 4u64) {Block<struct instrumentation_state>(array_shift<struct instrumentation_state>(&instrumentation, j))};
  //requires take ai = each(u64 j; j < 2u64) {Block<struct actuation_logic>(array_shift<struct actuation_logic>(&actuation_logic, j))};
    argc >= 0i32;
    take argvi = each (u64 i; i >= 0u64 && i < (u64)argc) {StringaRef(array_shift<char*>(argv,i))};

  ensures
    take co = Owned<struct core_state>(&core);
    take argvo = each (u64 i; i >= 0u64 && i < (u64)argc) {StringaRef(array_shift<char*>(argv,i))};
$*/
{
  //char **argv;
  //main_argv = argv;
#ifndef CN_ENV
  main_argv = argv;
  struct mps_command *cmd = (struct mps_command *)malloc(sizeof(*cmd));
#else
  struct mps_command _cmd;
  struct mps_command *cmd = &_cmd;
#endif

  core_init(&core);
  /*$ extract Block<struct instrumentation_state>, 0u64; $*/
  /*$ extract Block<struct actuation_logic>, 0u64; $*/
  sense_actuate_init(0, &instrumentation[0], &actuation_logic[0]);

  /*$ extract Block<struct instrumentation_state>, 2u64; $*/
  /*$ extract Block<struct actuation_logic>, 1u64; $*/
  sense_actuate_init(1, &instrumentation[2], &actuation_logic[1]);

  if (isatty(fileno(stdin))) printf("\e[1;1H\e[2J");
  if (isatty(fileno(stdin))) printf("\e[%d;3H\e[2K> ", NLINES+1);

#ifdef USE_PTHREADS
  pthread_attr_t attr;
  pthread_attr_init(&attr);
  int result;

  result = pthread_create(&sense_actuate_0_thread, &attr, start0, NULL);
  if (result != 0) {
    fprintf(stderr, "error %d creating sense_actuate_0 thread\n", result);
    clean_exit(1);
  }
  ++threads_started;

  result = pthread_create(&sense_actuate_1_thread, &attr, start1, NULL);
  if (result != 0) {
    fprintf(stderr, "error %d creating sense_actuate_1 thread\n", result);
    clean_exit(1);
  }
  ++threads_started;
#endif

  while (1) {
    char line[256];
    fflush(stdout);
    MUTEX_LOCK(&display_mutex);
    sprintf(line, "HW ACTUATORS %s %s", actuator_state[0] ? "ON " : "OFF", actuator_state[1]? "ON " : "OFF");
    set_display_line(&core.ui, 8, line, 0);
    MUTEX_UNLOCK(&display_mutex);
    update_instrumentation_errors();
    update_sensors();
    core_step(&core);
#ifndef USE_PTHREADS
    sense_actuate_step_0(&instrumentation[0], &actuation_logic[0]);
    sense_actuate_step_1(&instrumentation[2], &actuation_logic[1]);
#endif
    update_display();
    usleep(100);
  }

  clean_exit(0);
  return 0;
}

void clean_exit(int status) {
#ifdef USE_PTHREADS
  // Signal all sense_actuate threads to exit as soon as possible.
  running = 0;

  // Wait for all started threads to finish.  It's possible that not all
  // threads were started; if `main` encounters an error with `pthread_create`,
  // it calls `clean_exit` to shut down any previous threads before exiting.
  // We use the value of `threads_started` to determine which threads to join.
  if (threads_started >= 1) {
    pthread_join(sense_actuate_0_thread, NULL);
  }

  if (threads_started >= 2) {
    pthread_join(sense_actuate_1_thread, NULL);
  }
#endif

  exit(status);
};
