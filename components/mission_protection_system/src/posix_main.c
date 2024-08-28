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

int clear_screen() {
  return (isatty(fileno(stdin)) && (NULL == getenv("MPS_NOCLEAR")));
}

void update_display() {
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

void update_instrumentation_errors(void) {
  for (int i = 0; i < NINSTR; ++i) {
    if(error_instrumentation_mode[i] == 2) {
      error_instrumentation[i] |= rand() % 2;
    } else {
      error_instrumentation[i] = error_instrumentation_mode[i];
    }
  }
}

void update_sensor_errors(void) {
  for (int c = 0; c < 2; ++c) {
    for (int s = 0; s < 2; ++s) {
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

int update_sensor_simulation(void) {
  static int initialized = 0;
  static uint32_t last_update = 0;
  static uint32_t last[2][2] = {0};

  struct timespec tp;
  clock_gettime(CLOCK_REALTIME, &tp);
  uint32_t t0 = last_update;
  uint32_t t = tp.tv_sec*1000 + tp.tv_nsec/1000000;

  if (!initialized) {
    last_update = t;
    last[0][T] = T0;
    last[1][T] = T0;
    last[0][P] = P0;
    last[1][P] = P0;
    initialized = 1;
  } else if (t - t0 > SENSOR_UPDATE_MS) {
    for (int s = 0; s < 2; ++s) {
      last[s][T] += (rand() % 7) - 3 + T_BIAS;
      // Don't stray too far from our steam table
      last[s][T] = min(last[s][T], 300);
      last[s][T] = max(last[s][T], 25);

      last[s][P] += (rand() % 7) - 3 + P_BIAS;
      // Don't stray too far from our steam table
      last[s][P] = min(last[s][P], 5775200);
      last[s][P] = max(last[s][P], 8000);
    }
    last_update = t;
  }
  sensors[T][0] = last[T][0];
  sensors[T][1] = last[T][1];
  sensors[P][0] = last[P][0];
  sensors[P][1] = last[P][1];

  return 0;
}

void update_sensors(void) {
  update_sensor_errors();
#ifdef SIMULATE_SENSORS
  update_sensor_simulation();
#endif
  for (int c = 0; c < 2; ++c) {
    for (int s = 0; s < 2; ++s) {
      if (error_sensor[c][s]) {
        sensors[c][s] = rand();
      }

      MUTEX_LOCK(&mem_mutex);
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

int read_actuation_command(uint8_t id, struct actuation_command *cmd) {
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

struct sense_actuate_thread_state {
#ifdef USE_PTHREADS
    pthread_t thread;
    // Mutex controlling access to the `running` field.  All other fields are
    // accessed only by the main thread.
    pthread_mutex_t running_mutex;
    // Whether the thread should continue running.  The main thread sets this
    // to 0 when it's time for the other thread to shut down.
    int running;
    // If the thread is marked as `started`, then `clean_exit` will try to shut
    // it down.
    int started;
#else
    // In non-pthreads builds, this struct could be empty, except that
    // initializing an empty struct with `= { 0 }` triggers a warning.
    char dummy;
#endif
};
static struct sense_actuate_thread_state sense_actuate_0_state = { 0 };
static struct sense_actuate_thread_state sense_actuate_1_state = { 0 };

static int sense_actuate_thread_is_running(struct sense_actuate_thread_state* state) {
#ifdef USE_PTHREADS
  pthread_mutex_lock(&state->running_mutex);
  int running = state->running;
  pthread_mutex_unlock(&state->running_mutex);
  return running;
#else
  return 1;
#endif
}

void* start0(void *arg) {
  while (sense_actuate_thread_is_running(&sense_actuate_0_state)) {
    sense_actuate_step_0(&instrumentation[0], &actuation_logic[0]);
    usleep(100);
  }
  return NULL;
}
void* start1(void *arg) {
  while (sense_actuate_thread_is_running(&sense_actuate_1_state)) {
    sense_actuate_step_1(&instrumentation[2], &actuation_logic[1]);
    usleep(100);
  }
  return NULL;
}

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

int main(int argc, char **argv) {
  main_argv = argv;
  struct mps_command *cmd = (struct mps_command *)malloc(sizeof(*cmd));

  core_init(&core);
  sense_actuate_init(0, &instrumentation[0], &actuation_logic[0]);
  sense_actuate_init(1, &instrumentation[2], &actuation_logic[1]);

  if (isatty(fileno(stdin))) printf("\e[1;1H\e[2J");
  if (isatty(fileno(stdin))) printf("\e[%d;3H\e[2K> ", NLINES+1);

#ifdef USE_PTHREADS
  pthread_attr_t attr;
  pthread_attr_init(&attr);
  int result;

  pthread_mutex_init(&sense_actuate_0_state.running_mutex, NULL);
  sense_actuate_0_state.running = 1;
  result = pthread_create(&sense_actuate_0_state.thread, &attr, start0, NULL);
  if (result != 0) {
    fprintf(stderr, "error %d creating sense_actuate_0 thread\n", result);
    clean_exit(1);
  }
  sense_actuate_0_state.started = 1;

  pthread_mutex_init(&sense_actuate_1_state.running_mutex, NULL);
  sense_actuate_1_state.running = 1;
  result = pthread_create(&sense_actuate_1_state.thread, &attr, start1, NULL);
  if (result != 0) {
    fprintf(stderr, "error %d creating sense_actuate_1 thread\n", result);
    clean_exit(1);
  }
  sense_actuate_1_state.started = 1;
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
  if (sense_actuate_0_state.started) {
    pthread_mutex_lock(&sense_actuate_0_state.running_mutex);
    sense_actuate_0_state.running = 0;
    pthread_mutex_unlock(&sense_actuate_0_state.running_mutex);
    pthread_join(sense_actuate_0_state.thread, NULL);
  }

  if (sense_actuate_1_state.started) {
    pthread_mutex_lock(&sense_actuate_1_state.running_mutex);
    sense_actuate_1_state.running = 0;
    pthread_mutex_unlock(&sense_actuate_1_state.running_mutex);
    pthread_join(sense_actuate_1_state.thread, NULL);
  }
#endif

  exit(status);
};
