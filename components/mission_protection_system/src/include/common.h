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

#ifndef COMMON_H_
#define COMMON_H_

#include <stdint.h>

//////////////////////////////////////////////////////////////
// Constants derived from architecture and Cryptol model    //
//////////////////////////////////////////////////////////////

// Instrumentation
// Trip modes:
#define NINSTR 4
// These wrapper functions need their definitions exposed to CN, but must not
// cause multiple definition errors in the linker, so they must be static. They
// will not actually be called so this is OK.
/*$ function (u8) NINSTR() $*/
static
uint8_t c_NINSTR() /*$ cn_function NINSTR; $*/ { return NINSTR; }
#define NMODES 3
/*$ function (u8) NMODES() $*/
static
uint8_t c_NMODES() /*$ cn_function NMODES; $*/ { return NMODES; }
#define BYPASS 0
/*$ function (u8) BYPASS() $*/
static
uint8_t c_BYPASS() /*$ cn_function BYPASS; $*/ { return BYPASS; }
#define OPERATE 1
/*$ function (u8) OPERATE() $*/
static
uint8_t c_OPERATE() /*$ cn_function OPERATE; $*/ { return OPERATE; }
#define TRIP 2
/*$ function (u8) TRIP() $*/
static
uint8_t c_TRIP() /*$ cn_function TRIP; $*/ { return TRIP; }

// Command Types
#define SET_MODE 0
#define SET_MAINTENANCE 1
#define SET_SETPOINT 2

// Channel/Trip signal IDs
#define NTRIP 3
/*$ function (u8) NTRIP() $*/
static
uint8_t c_NTRIP() /*$ cn_function NTRIP; $*/ { return NTRIP; }
#define T 0
/*$ function (u8) T() $*/
static
uint8_t c_T() /*$ cn_function T; $*/ { return T; }
#define P 1
/*$ function (u8) P() $*/
static
uint8_t c_P() /*$ cn_function P; $*/ { return P; }
#define S 2
/*$ function (u8) S() $*/
static
uint8_t c_S() /*$ cn_function S; $*/ { return S; }

// Actuation
#define NVOTE_LOGIC 2
/*$ function (u8) NVOTE_LOGIC() $*/
static
uint8_t c_NVOTE_LOGIC() /*$ cn_function NVOTE_LOGIC; $*/ { return NVOTE_LOGIC; }
#define NDEV 2
/*$ function (u8) NDEV() $*/
static
uint8_t c_NDEV() /*$ cn_function NDEV; $*/ { return NDEV; }

// Core
// Command Types
#define INSTRUMENTATION_COMMAND 0
#define ACTUATION_COMMAND 1

#define BIT(_test, _value) ((_test) ? (0x8 | (_value)) : _value)
#define VALID(_value) (!(0x8 & (_value)))
#define VAL(_value) (0x1 & value)

#define NLINES 21
/*$ function (u8) NLINES() $*/
static
uint8_t c_NLINES() /*$ cn_function NLINES; $*/ { return NLINES; }
// we need 65 here because previously it was 64 + \n which was converted to
// \r\n, with a socket we need to put that \r
#define LINELENGTH 65
/*$ function (u64) LINELENGTH() $*/
static
uint64_t c_LINELENGTH() /*$ cn_function LINELENGTH; $*/ { return LINELENGTH; }

//////////////////////////////////////////////////////////////
// MPS Command Definitions                                  //
//////////////////////////////////////////////////////////////

// Instrumentation
struct set_mode {
  uint8_t channel;
  uint8_t mode_val;
};
struct set_maintenance {
  uint8_t on;
};
struct set_setpoint {
  uint8_t channel;
  uint32_t val;
};
struct instrumentation_command {
  uint8_t type;
  uint8_t valid;
#if !WAR_NO_UNIONS
  union {
#else
  struct {
#endif
    struct set_mode mode;
    struct set_maintenance maintenance;
    struct set_setpoint setpoint;
  } cmd;
};

// Actuation
struct actuation_command {
    uint8_t device;
    uint8_t on;
};

// Root command structure
struct mps_command {
  uint8_t type;
  uint8_t instrumentation_division;
#if !WAR_NO_UNIONS
  union {
#else
  struct {
#endif
    struct instrumentation_command instrumentation;
    struct actuation_command act;
  } cmd;
};

// Redefine variable bit-width types:
#define _ExtInt_1 char
#define _ExtInt_2 char
#define _ExtInt_3 char
#define _ExtInt_4 char
#define _ExtInt_6 char
#define _ExtInt_8 char
#define _ExtInt_32 int
#define _ExtInt(w) _ExtInt_##w

// Generate names for implementation variants
#define VARIANT(source,lang,f) VARIANT_IMPL(source,lang,f)
#define VARIANT_IMPL(source,lang,f) f ## _ ## source ## _ ## lang
#define VARIANT_IMPL2(source,lang,f) source ## lang ## f

void zero_u32_arr(uint32_t *a, unsigned int n);
/*$ spec zero_u32_arr(pointer a, u32 n);
  // @PropertyClass: P3-SOP
  // @PropertyClass: P2-LIV
  requires take ain = each(u64 i; i < (u64)n) { Block<uint32_t>(array_shift<uint32_t>(a, i))};
  ensures take aout = each(u64 i; i < (u64)n) { Owned<uint32_t>(array_shift<uint32_t>(a, i))};
 $*/

void zero_u8_arr(uint8_t *a, unsigned int n);
/*$ spec zero_u8_arr(pointer a, u32 n);
  // @PropertyClass: P3-SOP
  // @PropertyClass: P2-LIV
  requires take ain = each(u64 i; i < (u64)n) { Block<uint8_t>(array_shift<uint8_t>(a, i))};
  ensures take aout = each(u64 i; i < (u64)n) { Owned<uint8_t>(array_shift<uint8_t>(a, i))};
 $*/

#endif // COMMON_H_
