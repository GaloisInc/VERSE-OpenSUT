//time cn verify --magic-comment-char-dollar very_long.c --only=instrumentation_step
unsigned char T;
unsigned char P;
unsigned char S;

typedef unsigned char uint8_t;

typedef unsigned int uint32_t;





/*$ function (u8) NINSTR() $*/
static
uint8_t c_NINSTR() /*$ cn_function NINSTR; $*/ { return 4; }
/*$ function (u8) NMODES() $*/
static
uint8_t c_NMODES() /*$ cn_function NMODES; $*/ { return 3; }
/*$ function (u8) BYPASS() $*/
static
uint8_t c_BYPASS() /*$ cn_function BYPASS; $*/ { return 0; }
/*$ function (u8) OPERATE() $*/
static
uint8_t c_OPERATE() /*$ cn_function OPERATE; $*/ { return 1; }
/*$ function (u8) TRIP() $*/
static
uint8_t c_TRIP() /*$ cn_function TRIP; $*/ { return 2; }
/* $ function (bool) ModeOK(u8 mode) {
 (mode == BYPASS()) ||
 (mode == OPERATE()) ||
 (mode == TRIP())
} $*/
/*$ function (bool) ModeOK(u8 mode) {
  0u8 <= mode && mode < NMODES()
} $*/
/*$ function (u8) NTRIP() $*/
static
uint8_t c_NTRIP() /*$ cn_function NTRIP; $*/ { return 3; }
// Core
// Command Types
//////////////////////////////////////////////////////////////
// RTS Command Definitions                                  //
//////////////////////////////////////////////////////////////
// Instrumentation
struct instrumentation_command {
  uint8_t type;
};
struct instrumentation_state {
  //uint32_t reading[3];
  //uint32_t test_reading[3];
  //uint32_t setpoints[3];
  //uint8_t sensor_trip[3];
  //uint8_t a[3];
  //uint8_t b[3];
  //uint8_t c[1000];
  //uint8_t d;
  //uint8_t e;
  uint8_t mode[3];
};

int instrumentation_step(uint8_t div, struct instrumentation_state *state);

/*$ spec instrumentation_step(u8 div, pointer state);
    requires take statein = Owned<struct instrumentation_state>(state);
      each(u64 j; j < (u64)NTRIP()) {statein.mode[j] < NMODES()};
      ModeOK(statein.mode[0u64]);
      ModeOK(statein.mode[1u64]);
      ModeOK(statein.mode[2u64]);
      div < NTRIP();
    ensures
      take stateout = Owned<struct instrumentation_state>(state);
      each(u64 j; j < (u64)NTRIP()) {stateout.mode[j] < NMODES()};
      ModeOK(stateout.mode[0u64]);
      ModeOK(stateout.mode[1u64]);
      ModeOK(stateout.mode[2u64]);
$*/

int read_instrumentation_command(uint8_t division, struct instrumentation_command *cmd);
/*$ spec read_instrumentation_command(u8 division, pointer cmd);
    requires take cin = Block<struct instrumentation_command>(cmd);
      division < NINSTR();
    ensures take cout = Owned<struct instrumentation_command>(cmd);
      -1i32 <= return;
      return <= 1i32;
$*/

uint8_t is_test_running(void);
/*$ spec is_test_running();
    requires true;
    ensures true;
$*/

void get_test_instrumentation(uint8_t *id);
/*$ spec get_test_instrumentation(pointer id);
  requires take idin = each(u64 i; 0u64 <= i && i < 2u64) { Block<uint8_t>(array_shift(id, i)) };
  ensures take idout = each(u64 k; 0u64 <= k && k < 2u64) { Owned<uint8_t>(array_shift(id, k)) };
    each(u64 j; 0u64 <= j && j < 2u64) { idout[j] <= NINSTR() };
$*/
void set_instrumentation_test_complete(uint8_t div, int v);
/*$ spec set_instrumentation_test_complete(u8 div, i32 v);
    requires div < NINSTR();
    ensures true;
$*/

int is_instrumentation_test_complete(uint8_t id);
/*$ spec is_instrumentation_test_complete(u8 id);
    requires id < NINSTR();
    ensures true;
$*/

static int instrumentation_step_trip(uint8_t div,
                                     int do_test,
                                     struct instrumentation_state *state);
/*$ spec instrumentation_step_trip(u8 div, i32 do_test, pointer state);
    requires div < NINSTR();
      take si = Owned<struct instrumentation_state>(state);
      each(u64 i; 0u64 <= i && i < (u64)NTRIP()) {si.mode[i] < NMODES()};
    ensures take so = Owned<struct instrumentation_state>(state);
      -1i32 <= return; return <= 0i32;
      each(u64 j; 0u64 <= j && j < (u64)NTRIP()) {so.mode[j] < NMODES()};
$*/

static int instrumentation_handle_command(uint8_t div,
                                          struct instrumentation_command *i_cmd,
                                          struct instrumentation_state *state);
/*$ spec instrumentation_handle_command(u8 div, pointer i_cmd, pointer state);
    requires take ic_in = Owned<struct instrumentation_command>(i_cmd);
    take s_in = Owned<struct instrumentation_state>(state);

    each(u64 i; 0u64 <= i && i < (u64)NTRIP()) {s_in.mode[i] < NMODES()};
    ensures take ic_out = Owned<struct instrumentation_command>(i_cmd);
    take s_out = Owned<struct instrumentation_state>(state);
    return >= -1i32; return <= 0i32;
    each(u64 i; 0u64 <= i && i < (u64)NTRIP()) {s_out.mode[i] < NMODES()};
$*/

static int instrumentation_set_output_trips(uint8_t div,
                                            int do_test,
                                            struct instrumentation_state *state);
/*$ spec instrumentation_set_output_trips(u8 div, i32 do_test, pointer state);
    requires div < NINSTR();
    take si = Owned<struct instrumentation_state>(state);
    each(u64 i; 0u64 <= i && i < (u64)NTRIP()) {si.mode[i] < NMODES()};
    ensures return <= 0i32;
    take so = Owned<struct instrumentation_state>(state);
    each(u64 i; 0u64 <= i && i < (u64)NTRIP()) {so.mode[i] < NMODES()};
$*/

int instrumentation_step(uint8_t div, struct instrumentation_state *state) {
  int err = 0;
  uint8_t test_div[2];
  get_test_instrumentation(test_div);
  /*$ extract Owned<uint8_t>, 0u64; $*/
  /*$ extract Owned<uint8_t>, 1u64; $*/
  int do_test = (div == test_div[0] || div == test_div[1]) && is_test_running();
  //if (do_test && is_instrumentation_test_complete(div))
    //return 0;
  if (!do_test && is_instrumentation_test_complete(div)) {
    set_instrumentation_test_complete(div, 0);
  }

  err |= instrumentation_step_trip(div, do_test, state);

  struct instrumentation_command i_cmd;
  int read_cmd = read_instrumentation_command(div, &i_cmd);
  if (read_cmd > 0) {
    err |= instrumentation_handle_command(div, &i_cmd, state);
  } else if (read_cmd < 0) {
    err |= -read_cmd;
  }

  err |= instrumentation_set_output_trips(div, do_test, state);
  /*$ instantiate 0u64; $*/
  /*$ instantiate 1u64; $*/
  /*$ instantiate 2u64; $*/
  return err;
}
