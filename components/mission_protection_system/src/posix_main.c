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

#ifndef CN_ENV
// Cerberus has these headers but they're not accessible, CN issue #358
#if 0
#include <posix/poll.h>
#include <posix/fcntl.h>
#include <posix/termios.h>
#include <posix/unistd.h>
#include <posix/sys/select.h>
#include <posix/time.h>
#else
#include <poll.h>
#include <fcntl.h>
#include <termios.h>
#include <unistd.h>
#include <sys/select.h>
#include <time.h>

#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <unistd.h>
#include <assert.h>
#include <sys/socket.h>
#include <sys/types.h>
#include <sys/un.h>

#endif
#include <poll.h>
#include <fcntl.h>
#endif
#include <stdio.h>
#ifndef CN_ENV
#include <termios.h>
#include <unistd.h>
#endif
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#ifdef CN_ENV
#include <posix/sys/socket.h>
#include <posix/sys/types.h>
#endif
#ifndef CN_ENV
#include <sys/select.h>
#include <time.h>
#endif

#ifdef CN_ENV
#include "cn_strings.h"
#include "cn_memory.h"
#define malloc(x) _malloc(x)
#define free(x) _free(x)
#include "cn_sys.h"
#define read(f,b,s) _read(f,b,s)
#define write(f,b,s) _write(f,b,s)
#endif

#ifdef WAR_CN_358
#define STDIN_FILENO 0
int
isatty(int fd);
int
fileno(FILE *stream);
// this spec satisfies the caller but requires we have evidence that stdin is
// alive, and might need to be extended to provide evidence that the argument is
// open for full compliance.
/*$ spec fileno(pointer stream);
    // @PropertyClass: P3-SOP
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
/*$ spec poll(pointer fds, u64 nfds, i32 timeout);
  // @PropertyClass: P3-SOP
  requires take fdsi = each(u64 i; i < nfds) {Owned<struct pollfd>(array_shift(fds, i))};
  ensures take fdso = each(u64 i; i < nfds) {Owned<struct pollfd>(array_shift(fds, i))};
$*/

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
    // @PropertyClass: P3-SOP
    requires take tpi = Block<struct timespec>(tp);
    ensures take tpo = Owned<struct timespec>(tp);
$*/

int
rand(void);
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
/*$ spec remove(pointer filename);
  requires true;
  ensures true;
$*/
/*$ spec strcpy(pointer dst, pointer src);
  requires true;
  ensures true;
$*/

// TODO spec for returning a statically allocated string
/*$ spec getenv(pointer n);
  requires true;
  ensures true;
$*/

ssize_t
getline(char ** restrict linep, size_t * restrict linecapp,
        FILE * restrict stream);
/*$ spec getline(pointer linep, pointer linecapp, pointer stream);
  // @PropertyClass: P3-SOP
  // @PropertyClass: P6-UserDefPred
  requires
    take args = GetLineArgs(linep, linecapp);
  ensures
    take res = GetLineResult(linep, linecapp, return);
$*/
typedef size_t socklen_t;
int
socket(int domain, int type, int protocol);
/*$ spec socket(i32 domain, i32 type, i32 protocol);
  requires true;
  ensures true;
$*/

typedef int sa_family_t;
struct sockaddr {
  sa_family_t sun_family;
  char sa_data[104];
};


struct sockaddr_un {
  sa_family_t sun_family;
  char sun_path[104];
};
int
bind(int socket, const struct sockaddr *address, socklen_t address_len);
/*$ spec bind(i32 sock, pointer address, u64 address_len);
  requires true;
  ensures true;
$*/
int
listen(int socket, int backlog);
/*$ spec listen(i32 sock, i32 backlog);
  requires true;
  ensures true;
$*/
int
accept(int socket, struct sockaddr *restrict address,
       socklen_t *restrict address_len);
/*$ spec accept(i32 sock, pointer address, pointer address_len);
  requires true;
  ensures true;
$*/

#define AF_UNIX 1
#define SOCK_STREAM 2
int
usleep(useconds_t microseconds);
#endif


int mps_cmd_fd;

extern struct instrumentation_state instrumentation[4];
struct actuation_command *act_command_buf[2];
#define min(_a, _b) ((_a) < (_b) ? (_a) : (_b))
#define max(_a, _b) ((_a) > (_b) ? (_a) : (_b))
#ifndef CN_ENV
//cerberus has a pthread header but like the others it's not accessible
#include <pthread.h>
pthread_mutex_t display_mutex = PTHREAD_MUTEX_INITIALIZER;
pthread_mutex_t mem_mutex = PTHREAD_MUTEX_INITIALIZER;
#endif

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
/*$
  // @PropertyClass: P3-SOP
  accesses __stdin;
$*/
{
  return (isatty(fileno(stdin)) && (NULL == getenv("MPS_NOCLEAR")));
}

void update_display()
#if !WAR_CN_399
/*$
  // @PropertyClass: P3-SOP
  accesses __stdin;
$*/
#else
  /*$ trusted; $*/
#endif
{
  if (!mps_cmd_fd) {
    if (clear_screen()) {
      printf("\x1b[s\x1b[1;1H");//\e[2J");
    }
  }
  for (int line = 0; line < NLINES; ++line) {
    if (!mps_cmd_fd) {
      printf("\x1b[0K");
      printf("%s%s", core.ui.display[line], line == NLINES-1 ? "" : "\n");
    } else {
      char l[LINELENGTH+1] = {0};
      int n = snprintf(l, sizeof(l), "%s%s", core.ui.display[line], "\r\n");
      if (l[0] == 'L') {
        printf("%s%s", core.ui.display[line], line == NLINES-1 ? "" : "\n");
      }
      write(mps_cmd_fd, l, n);
    }
  }
  if (!mps_cmd_fd) {
    if (clear_screen()) {
      printf("\x1b[u");
    }
  }
}

// A copy of the `argv` that was passed to main.  This is used to implement the
// reset (`R`) command inside `read_mps_command`.
static char** main_argv = NULL;

char * read_line_stdio(void)
/*$
  // @PropertyClass: P3-SOP
  // @PropertyClass: P6-UserDefPred
  accesses __stdin;
  ensures
    take out = OptionAllocatedString(return);
$*/
{
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
  /*$ extract Owned<struct pollfd>, 0u64; $*/
  struct pollfd *fds_ = &fds;
  if(poll(&fds, 1, 100) < 1) {
    return 0;
  }
  linelen = getline(&line, &linecap, stdin);

  if (linelen == EOF)
    clean_exit(0);

  if (linelen < 0)
    return NULL;

  // required because we don't have a predicate for returning a partially-initialized string
  /*$ apply ViewShift_Block_u8(line, array_shift(line, (u64)linelen), (u64)linelen, linecap-(u64)linelen); $*/
  memset(&line[linelen], 0, linecap-linelen);
  /*$ apply UnViewShift_Owned_u8(line, array_shift(line, (u64)linelen), (u64)linelen, linecap-(u64)linelen); $*/
  /*$ apply JoinSlice_Owned_u8(line, 0u64, linecap, (u64)linelen); $*/
  return line;
}

void setup_mps_socket(void)
/*$
  // @PropertyClass: P3-SOP
  accesses mps_cmd_fd;
$*/
{
  int server_socket_fd;
  struct sockaddr_un sockaddr_un = {0};
  int return_value;
  char *socket_address = getenv("MPS_CMD_SOCKET");
  if (socket_address == NULL) {
    return;
  }

  server_socket_fd = socket( AF_UNIX, SOCK_STREAM, 0 );
  if ( server_socket_fd == -1 ) {
    DEBUG_PRINTF(("failed to create socket %d", errno));
    clean_exit(1);
  }

  remove( socket_address );

  sockaddr_un.sun_family = AF_UNIX;
  strcpy( sockaddr_un.sun_path, socket_address );
  struct sockaddr_un saddr = sockaddr_un;

  return_value =
    bind(
      server_socket_fd,
       (const struct sockaddr*)(struct sockaddr*)&saddr,
      sizeof( struct sockaddr_un ) );

  if ( return_value == -1 ) {
    DEBUG_PRINTF(("failed to bind the mps socket %d", errno));
    clean_exit(1);
  }

  if ( listen( server_socket_fd, 4096 ) == -1 ) {
    DEBUG_PRINTF(("failed to listen to the mps socket %d", errno));
    clean_exit(1);
  }

  int accept_socket_fd = 0;

  while (1)
  /* $ inv
    true;
  $*/
  {
    accept_socket_fd = accept( server_socket_fd, NULL, NULL );
    if ( accept_socket_fd == -1 ) {
      DEBUG_PRINTF(("failed to accept the mps socket %d", errno));
      clean_exit(1);
    }

    if ( accept_socket_fd > 0 ) { /* client is connected */
      mps_cmd_fd = accept_socket_fd;
      break;
    }
  }
}

char *read_line_socket(void)
/*$
  // @PropertyClass: P2-LIV
  // @PropertyClass: P3-SOP
  // @PropertyClass: P6-UserDefPred
  accesses mps_cmd_fd;
  ensures take out = OptionAllocatedString(return);
$*/
{
  if (mps_cmd_fd == 0) {
    return NULL;
  }
  struct pollfd fds;
  struct pollfd *fds_ = &fds;
  fds.fd = mps_cmd_fd;
  fds.events = POLLIN;
  fds.revents = POLLIN;
  /*$ extract Owned<struct pollfd>, 0u64; $*/
  if(poll(&fds, 1, 100) < 1) {
    return 0;
  }

  char *input_buffer = NULL;
  size_t buffer_size = 256;
  size_t init = 0;
  input_buffer = malloc(buffer_size);
  if (!input_buffer) {
    return NULL;
  }

  while (1)
  /*$ inv
    init <= buffer_size;
    take al = Alloc(input_buffer);
    al.base == (u64)input_buffer;
    al.size == buffer_size;
    take oi = ArraySliceOwned_u8(input_buffer, 0u64, init);
    take bi = ArraySliceBlock_u8(input_buffer, init, buffer_size);
  $*/
  {
    if (init == buffer_size) {
      /*$ apply JoinSlice_Block_u8(input_buffer, 0u64, buffer_size, init); $*/
      free(input_buffer);
      return NULL;
    }
    // [0, init) owned
    // [init, buffer_size) block

    /*$ apply ViewShift_Block_u8(input_buffer, array_shift(input_buffer, init), init, buffer_size-init); $*/
    ssize_t n = read( mps_cmd_fd, &input_buffer[init], buffer_size-init);
    if (n == 0) {
      DEBUG_PRINTF(("read_mps_socket: EOF\n"));
      /*$ apply UnViewShift_Block_u8(input_buffer, array_shift(input_buffer, init), init, buffer_size-init); $*/
      /*$ apply JoinSlice_Block_u8(input_buffer, 0u64, buffer_size, init); $*/
      free(input_buffer);
      return NULL;
      clean_exit(0);
      //__builtin_unreachable();
    } else if (n < 0) {
      DEBUG_PRINTF(("read_mps_socket: error %d\n", errno));
      /*$ apply UnViewShift_Block_u8(input_buffer, array_shift(input_buffer, init), init, buffer_size-init); $*/
      /*$ apply JoinSlice_Block_u8(input_buffer, 0u64, buffer_size, init); $*/
      free(input_buffer);
      return NULL;
      clean_exit(0);
      //__builtin_unreachable();
    } else {
      /*$ apply UnViewShift_Owned_u8(input_buffer, array_shift(input_buffer, init), init, (u64)n); $*/
      /*$ apply UnViewShift_Block_At_u8(input_buffer, array_shift(input_buffer, init), init, (u64)n, buffer_size-init); $*/
      /*$ apply JoinSlice_Owned_u8(input_buffer, 0u64, init+(u64)n, init); $*/
      init += n;
    }

    ///*$ split_case(n <= -1i64 ); $*/
    char *nl = memchr(input_buffer, '\n', init);
    ///*$ apply UnSplitAt_Owned_u8(input_buffer, buffer_size, init, buffer_size-init); $*/
    if (nl) {
      // TODO necessary because there is no way to pass back a
      // partially-initialized buffer with an unspecified initialized length
      // currently
      /*$ apply ViewShift_Block_u8(input_buffer, array_shift(input_buffer, init), init, buffer_size-init); $*/
      memset(&input_buffer[init], 0, buffer_size-init);
      /*$ apply UnViewShift_Owned_u8(input_buffer, array_shift(input_buffer, init), init, buffer_size-init); $*/
      /*$ apply JoinSlice_Owned_u8(input_buffer, 0u64, buffer_size, init); $*/
      return input_buffer;
    }
  }
}

#ifndef CN_ENV
//can get around everything but sscanf which is variadic and can't be worked
//around with a dummy because it's actually used at multiple types here
int read_mps_command(struct mps_command *cmd) {
  int ok = 0;
  uint8_t device, on, div, ch, mode, sensor;
  uint32_t val;
  char *line = NULL;

  if (!mps_cmd_fd) {
    line = read_line_stdio();
  } else {
    line = read_line_socket();
  }

  if (!line) {
    return 0;
  }

  MUTEX_LOCK(&display_mutex);

  if (clear_screen()) {
    printf("\x1b[%d;1H\x1b[2K> ", NLINES+1);
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
    // TODO call a noreturn function
    #ifndef CN_ENV
    execv("/proc/self/exe", main_argv);
    #else
    exit(0);
    #endif
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
#endif

void update_instrumentation_errors(void)
/*$
  // @PropertyClass: P2-LIV
  // @PropertyClass: P3-SOP
  accesses error_instrumentation_mode;
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
  // @PropertyClass: P2-LIV
  // @PropertyClass: P3-SOP
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
#ifdef CN_ENV
static int initialized = 0;
static uint32_t last_update = 0;
static uint32_t last[2][2] = {0};
#endif
int update_sensor_simulation(void)
#if !WAR_CN_399
  /*$
  // @PropertyClass: P2-LIV
  // @PropertyClass: P3-SOP
    accesses last_update;
    accesses initialized;
    accesses last;
    accesses sensors;
    $*/
#else
/*$ trusted; $*/
#endif
{
  #ifndef CN_ENV
  static int initialized = 0;
  static uint32_t last_update = 0;
  static uint32_t last[2][2] = {0};
  #endif

  struct timespec tp;
  clock_gettime(CLOCK_REALTIME, &tp);
  uint32_t t0 = last_update;

#ifndef CN_ENV
  uint32_t t = tp.tv_sec*1000 + tp.tv_nsec/1000000;
#else
  uint32_t t = 0;
  /*$ split_case(tp.tv_sec > 1000000i64 || tp.tv_sec < -1000000i64); $*/
  if (tp.tv_sec > 1000000 || tp.tv_sec < -1000000) {
    initialized = 0;
  } else {
   t = tp.tv_sec*1000 + tp.tv_nsec/1000000;
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
/*$
  // @PropertyClass: P2-LIV
  // @PropertyClass: P3-SOP
  accesses error_sensor;
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
#ifdef USE_PTHREADS
static _Atomic int running = 1;
// Number of threads started successfully.
static int threads_started = 0;
static pthread_t sense_actuate_0_thread = { 0 };
static pthread_t sense_actuate_1_thread = { 0 };

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
#endif

#if WAR_CN_353
  time_t start_time = 0;
#endif
// TODO ensure names match gcc builtins
int sadd_overflow (int a, int b, int *res);
/*$ spec sadd_overflow(i32 a, i32 b, pointer res);
  // @PropertyClass: P1-LAC
  // @PropertyClass: P3-SOP
    requires take x = Block<int>(res);
    ensures take out = Owned<int>(res);
      (return == (1i32)) || (out == (a + b));
$*/
int smul_overflow (int a, int b, int *res);
/*$ spec smul_overflow(i32 a, i32 b, pointer res);
  // @PropertyClass: P1-LAC
  // @PropertyClass: P3-SOP
    requires take x = Block<int>(res);
    ensures take out = Owned<int>(res);
      (return == (1i32)) || (out == (a * b));
$*/
int ssub_overflow (int a, int b, int *res);
/*$ spec ssub_overflow(i32 a, i32 b, pointer res);
  // @PropertyClass: P1-LAC
  // @PropertyClass: P3-SOP
    requires take x = Block<int>(res);
    ensures take out = Owned<int>(res);
      (return == (1i32)) || (out == (a - b));
$*/
int dadd_overflow (int64_t a, int64_t b, int64_t *res);
/*$ spec dadd_overflow(i64 a, i64 b, pointer res);
  // @PropertyClass: P1-LAC
  // @PropertyClass: P3-SOP
    requires take x = Block<int64_t>(res);
    ensures take out = Owned<int64_t>(res);
      (return == (1i32)) || (out == (a + b));
$*/
int dmul_overflow (int64_t a, int64_t b, int64_t *res);
/*$ spec dmul_overflow(i64 a, i64 b, pointer res);
  // @PropertyClass: P1-LAC
  // @PropertyClass: P3-SOP
    requires take x = Block<int64_t>(res);
    ensures take out = Owned<int64_t>(res);
      (return == (1i32)) || (out == (a * b));
$*/
int dsub_overflow (int64_t a, int64_t b, int64_t *res);
/*$ spec dsub_overflow(i64 a, i64 b, pointer res);
  // @PropertyClass: P1-LAC
  // @PropertyClass: P3-SOP
    requires take x = Block<int64_t>(res);
    ensures take out = Owned<int64_t>(res);
      (return == (1i32)) || (out == (a - b));
$*/
uint32_t time_in_s()
{
  #if !WAR_CN_353
  static time_t start_time = 0;
  #else
  time_t start_time = 0;
  #endif
  struct timespec tp;
  clock_gettime(CLOCK_REALTIME, &tp);
  /*$ split_case(start_time == 0i64); $*/
  if (start_time == 0) {
    start_time = tp.tv_sec;
  }
  #ifndef CN_ENV
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

// TODO core_state_ok({0}) must be true

// VERSE-Toolchain#107 is the blocker here

int main(int argc, char **argv)
/*$
  // @PropertyClass: P3-SOP
  // @PropertyClass: P6-UserDefPred
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
  main_argv = argv;
#ifndef CN_ENV
  struct mps_command *cmd = (struct mps_command *)malloc(sizeof(*cmd));
#else
  struct mps_command _cmd;
  struct mps_command *cmd = &_cmd;
#endif

  DEBUG_PRINTF("about to create mps socket\n");
  setup_mps_socket();
  DEBUG_PRINTF("done creating mps socket\n");
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
}
