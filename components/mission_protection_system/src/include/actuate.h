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

#ifndef ACTUATE_H_
#define ACTUATE_H_

#include <stdint.h>
#include "models.acsl"

// Combine the votes from both actuate logic components
// and tell the hardware device to actuate (or unactuate)
int actuate_devices(void);
/*$ spec actuate_devices();
  // @PropertyClass: P2-LIV
  // @PropertyClass: P3-SOP
    requires
      take ci = Owned<struct core_state>(&core);
      //core_state_ok(ci);
      take dali = Owned<uint8_t[2][2]>(&device_actuation_logic);
      take asi = Owned<uint8_t[4]>(&actuator_state);
    ensures
      take co = Owned<struct core_state>(&core);
      //core_state_ok(co);
      take dalo = Owned<uint8_t[2][2]>(&device_actuation_logic);
      take aso = Owned<uint8_t[4]>(&actuator_state);
$*/

// Return whether or not a device with the provided votes should be actuated
// Bit i = vote by logic unit i
// This function is generated directly from the Cryptol model
/*@ assigns \nothing;
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 <==> ((vs & 0x01) || (vs & 0x02));
  @ ensures ActuateActuator(vs) <==> \result == 1;
*/
uint8_t ActuateActuator(uint8_t vs);
/*$ spec ActuateActuator(u8 vs);
  // @PropertyClass: P5-UDFunc
    requires true;
    ensures (return == 0u8 || return == 1u8);
      (return == 1u8) == (bw_and_uf(vs, 1u8) != 0u8 || bw_and_uf(vs, 2u8) != 0u8);
      ActuateActuator(vs) == (return == 1u8);
 $*/

int actuate_devices_generated_C(void);

#endif // ACTUATE_H_
