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

#include "common.h"
#include "core.h"
#include "instrumentation.h"
#include "actuation_logic.h"
#include "sense_actuate.h"
#include "platform.h"

#if 0
// Cerberus has these headers but they're not accessible, CN issue #358
#include <posix/poll.h>
#include <posix/fcntl.h>
#include <posix/termios.h>
#include <posix/unistd.h>
#include <posix/sys/select.h>
#include <posix/time.h>
#endif
#if 0
#include <poll.h>
#include <fcntl.h>
#endif
#if !WAR_NO_VARIADICS
#include <stdio.h>
#else
#define printf(...)
#define sprintf(...)
#endif
#if 0
#include <termios.h>
#include <unistd.h>
#endif
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#if 0
#include <sys/select.h>
#include <time.h>
#endif

#if 1
// these are just placeholder definitions until CN #358 is done
typedef signed int ssize_t;
typedef int64_t time_t;
typedef struct FILE {
  int x;
} FILE;
FILE _stdin;
FILE *__stdin = &_stdin;
// this is how the cerberus stdio does it
#define stdin __stdin
FILE *stdout;
#define STDIN_FILENO 0
#define EOF 0x100
int
isatty(int fd);
int
fileno(FILE *stream);
// this spec satisfies the caller but requires we have evidence that stdin is
// alive, and might need to be extended to provide evidence that the argument is
// open for full compliance.
/*$ spec fileno(pointer stream);
    requires take si = Owned<FILE>(stream);
    ensures take so = Owned<FILE>(stream);
$*/
int
fflush(FILE *stream);

#define POLLIN 0
struct pollfd {
  int    fd;       /* file descriptor */
  short  events;   /* events to look for */
  short  revents;  /* events returned */
};
typedef size_t nfds_t;
int
poll(struct pollfd fds[], nfds_t nfds, int timeout);

struct timespec {
  int64_t tv_usec;
  int64_t tv_nsec;
  int64_t tv_sec;
};

typedef int clockid_t;
#define CLOCK_REALTIME 0
int
clock_gettime(clockid_t clock_id, struct timespec *tp);
/*$ spec clock_gettime(i32 clock_id, pointer tp);
    requires take tpi = Block<struct timespec>(tp);
    ensures take tpo = Owned<struct timespec>(tp);
$*/

int
rand(void);
/*$ spec rand();
    requires true;
    ensures true;
$*/

typedef int64_t useconds_t;
int
usleep(useconds_t microseconds);
#endif


extern struct instrumentation_state instrumentation[4];
struct actuation_command *act_command_buf[2];
#define min(_a, _b) ((_a) < (_b) ? (_a) : (_b))
#define max(_a, _b) ((_a) > (_b) ? (_a) : (_b))
#if 0
//cerberus has a pthread header but like the others it's not accessible
#include <pthread.h>
pthread_mutex_t display_mutex = PTHREAD_MUTEX_INITIALIZER;
pthread_mutex_t mem_mutex = PTHREAD_MUTEX_INITIALIZER;
#endif

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
  return (isatty(fileno(stdin)) && (NULL == getenv("RTS_NOCLEAR")));
}

void update_display()
  /*$ accesses __stdin; $*/
{
  if (clear_screen()) {
    printf("\x1b[s\x1b[1;1H");//\e[2J");
  }
  for (int line = 0; line < NLINES; ++line) {
    printf("\x1b[0K");
    printf("%s%s", core.ui.display[line], line == NLINES-1 ? "" : "\n");
  }
  if (clear_screen()) {
    printf("\x1b[u");
  }
}

// A copy of the `argv` that was passed to main.  This is used to implement the
// reset (`R`) command inside `read_rts_command`.
static char** main_argv = NULL;

#if 0
//can get around everything but sscanf which is variadic and can't be worked
//around with a dummy because it's actually used at multiple types here
int read_rts_command(struct rts_command *cmd) {
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
    exit(0);

  if (linelen < 0)
    return 0;

  MUTEX_LOCK(&display_mutex);

  if (clear_screen()) {
    printf("\x1b[%d;1H\x1b[2K> ", NLINES+1);
  }

  MUTEX_UNLOCK(&display_mutex);

  if (2 == (ok = sscanf(line, "A %hhd %hhd", &device, &on))) {
    cmd->type = ACTUATION_COMMAND;
    cmd->cmd.act.device = device;
    cmd->cmd.act.on = on;
    DEBUG_PRINTF(("<main.c> read_rts_command ACTUATION_COMMAND dev=%u on=%u\n",
                  cmd->cmd.act.device, cmd->cmd.act.on));
    ok = 1;
  } else if (2 == (ok = sscanf(line, "M %hhd %hhd", &div, &on))) {
    cmd->type = INSTRUMENTATION_COMMAND;
    cmd->instrumentation_division = div;
    cmd->cmd.instrumentation.type = SET_MAINTENANCE;
    cmd->cmd.instrumentation.cmd.maintenance.on = on;
    DEBUG_PRINTF(("<main.c> read_rts_command INSTRUMENTATION_COMMAND MAINTENANCE div=%u on=%u, type=%u\n",
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
    DEBUG_PRINTF(("<main.c> read_rts_command INSTRUMENTATION_COMMAND MODE div=%u channel=%u mode=%u type=%u\n",
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
    DEBUG_PRINTF(("<main.c> read_rts_command INSTRUMENTATION_COMMAND SETPOINT div=%u channel=%u val=%u\n",
                  cmd->instrumentation_division,
                  cmd->cmd.instrumentation.cmd.setpoint.channel,
                  cmd->cmd.instrumentation.cmd.setpoint.val));
    ok = 1;
#ifndef SIMULATE_SENSORS
  } else if (3 == (ok = sscanf(line, "V %hhd %hhd %d", &sensor, &ch, &val))) {
    if (sensor < 2 && ch < 2)
      sensors[ch][sensor] = val;
    DEBUG_PRINTF(("<main.c> read_rts_command UPDATE SENSORS sensor=%d, ch=%d, val=%d\n",
          sensor,ch,val));
#endif
  } else if (line[0] == 'Q') {
    printf("<main.c> read_rts_command QUIT\n");
    exit(0);
  } else if (line[0] == 'R') {
    printf("<main.c> read_rts_command RESET\n");
    // Re-exec the RTS binary with the same arguments and environment.  This
    // has the effect of resetting the entire RTS to its initial state.
    // TODO call a noreturn function
    #if 0
    execv("/proc/self/exe", main_argv);
    #else
    exit(0);
    #endif
  } else if (line[0] == 'D') {
    DEBUG_PRINTF(("<main.c> read_rts_command UPDATE DISPLAY\n"));
    update_display();
  } else if (3 == (ok = sscanf(line, "ES %hhd %hhd %hhd", &sensor, &ch, &mode))) {
    error_sensor_mode[ch][sensor] = mode;
    DEBUG_PRINTF(("<main.c> read_rts_command ERROR SENSOR sensor=%d, ch=%d, mode=%d\n",
          sensor,ch,mode));
  } else if (2 == (ok = sscanf(line, "EI %hhd %hhd", &div, &mode))) {
    error_instrumentation_mode[div] = mode;
    DEBUG_PRINTF(("<main.c> read_rts_command ERROR INSTRUMENTATION div=%d, mode=%d\n",
          div,mode));
  }

  if (line)
    free(line);

  return ok;
}
#endif

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
#if !WAR_CN_231
      error_instrumentation[i] |= rand() % 2;
#else
      error_instrumentation[i] |= rand() & 1;
#endif
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
          #if 0
          int fail = rand() % 2;
          #else
          int fail = rand() & 1;
          #endif
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

// CN #353 is blocking this, additionally it will require careful handling of
// the arithmetic which has many possible overflows
#if 1
static int initialized = 0;
static uint32_t last_update = 0;
static uint32_t last[2][2] = {0};
#endif
int update_sensor_simulation(void)
  /*$
    accesses last_update;
    accesses initialized;
    accesses last;
    accesses sensors;
    $*/
{
  #if 0
  static int initialized = 0;
  static uint32_t last_update = 0;
  static uint32_t last[2][2] = {0};
  #endif

  struct timespec tp;
  clock_gettime(CLOCK_REALTIME, &tp);
  uint32_t t0 = last_update;

#if 0
  uint32_t t = tp.tv_sec*1000 + tp.tv_nsec/1000000;
#else
  uint32_t t = 0;
  /*$ split_case(tp.tv_sec > 1000000i64 || tp.tv_sec < -1000000i64); $*/
  if (tp.tv_sec > 1000000 || tp.tv_sec < -1000000) {
    initialized = 0;
  } else {
#if !WAR_CN_231
   t = tp.tv_sec*1000 + tp.tv_nsec/1000000;
#else
   t = tp.tv_sec*1000; //+ tp.tv_nsec;
#endif
  }
#endif

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
#if !WAR_CN_231
      last[s][T] += (rand() % 7) - 3 + T_BIAS;
#else
      last[s][T] += (rand()) - (uint32_t)3 + T_BIAS;
#endif
      // Don't stray too far from our steam table
      last[s][T] = min(last[s][T], 300);
      last[s][T] = max(last[s][T], 25);

      /*$ extract Owned<uint32_t>, (u64)P(); $*/
#if !WAR_CN_231
      last[s][P] += (rand() % 7) - 3 + P_BIAS;
#else
      last[s][P] += (rand()) - (uint32_t)3 + P_BIAS;
#endif
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
      ///*$ extract Owned<uint32_t[2]>, (u64)c; $*/
      ///*$ extract Owned<uint32_t>, (u64)s; $*/
        //sensors[c][s] = rand();
      }

      MUTEX_LOCK(&mem_mutex);

      /*$ extract Owned<uint32_t[2][2]>, (u64)c; $*/
      /*$ extract Owned<uint32_t[2]>, (u64)s; $*/
      /*$ extract Owned<uint32_t>, 0u64; $*/
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

void* start0(void *arg) {
  while(1) {
    sense_actuate_step_0(&instrumentation[0], &actuation_logic[0]);
    usleep(100);
  }
}
void* start1(void *arg) {
  while(1) {
    sense_actuate_step_1(&instrumentation[2], &actuation_logic[1]);
    usleep(100);
  }
}

#if 1
  time_t start_time = 0;
#endif
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
/*$ accesses start_time;
    accesses core;
$*/
{
  #if 0
  static time_t start_time = 0;
  #endif
  struct timespec tp;
  clock_gettime(CLOCK_REALTIME, &tp);
  /*$ split_case(start_time == 0i64); $*/
  if (start_time == 0) {
    start_time = tp.tv_sec;
  }
  #if 0
  time_t total = tp.tv_sec - start_time;
  #else
  int64_t total_ = 0;
  time_t total = 0;
  int ok = dsub_overflow(tp.tv_sec, start_time, &total_);
  total = total_;
  #endif
  char line[256];
  sprintf(line, "Uptime: [%u]s\n",(uint32_t)total);
  set_display_line(&core.ui, 9, line, 0);
  return (uint32_t)total;
}

// VERSE-Toolchain#107 is the blocker here

int main(void) //(int argc, char **argv)
/*$  requires true;
  ////requires take ci = Block<struct core_state>(&core);
  //requires take ii = each(u64 j; j < 4u64) {Block<struct instrumentation_state>(array_shift<struct instrumentation_state>(&instrumentation, j))};
  //requires take ai = each(u64 j; j < 2u64) {Block<struct actuation_logic>(array_shift<struct actuation_logic>(&actuation_logic, j))};
    ensures true;
$*/
{
  //char **argv;
  //main_argv = argv;
#if 0
  struct rts_command *cmd = (struct rts_command *)malloc(sizeof(*cmd));
#else
  struct rts_command _cmd;
  struct rts_command *cmd = &_cmd;
#endif

  core_init(&core);
  /*$ extract Block<struct instrumentation_state>, 0u64; $*/
  /*$ extract Block<struct actuation_logic>, 0u64; $*/
  sense_actuate_init(0, &instrumentation[0], &actuation_logic[0]);

  /*$ extract Block<struct instrumentation_state>, 2u64; $*/
  /*$ extract Block<struct actuation_logic>, 1u64; $*/
  sense_actuate_init(1, &instrumentation[2], &actuation_logic[1]);

  if (isatty(fileno(stdin))) printf("\x1b[1;1H\x1b[2J");
  if (isatty(fileno(stdin))) printf("\x1b[%d;3H\x1b[2K> ", NLINES+1);

#ifdef USE_PTHREADS
  pthread_attr_t attr;
  pthread_t sense_actuate_0, sense_actuate_1;
  pthread_attr_init(&attr);
  pthread_create(&sense_actuate_0, &attr, start0, NULL);
  pthread_create(&sense_actuate_1, &attr, start1, NULL);
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

  return 0;
}
