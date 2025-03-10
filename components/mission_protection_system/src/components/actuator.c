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

#include "platform.h"
#include "actuate.h"
#include "actuation_logic.h"

#ifdef PLATFORM_HOST
// CN currently does not support <stdio.h>
// see https://github.com/rems-project/cerberus/issues/277
// for details
#include <stdio.h>
#else // PLATFORM_HOST not defined
#include "printf.h"
#endif // ifdef PLATFORM_HOST

#define w1 uint8_t
#define w2 uint8_t

/*@ requires \true;
  @ assigns core.test.test_device_done[0..2];
  @ assigns core.test.test_device_result[0..2];
  @ ensures \true;
*/
int actuate_devices(void)
{
  int err = 0;
  int do_test = is_test_running() && is_actuation_unit_test_complete(get_test_actuation_unit());
  DEBUG_PRINTF(("<actuator.c> actuate_devices, do_test = %i\n",do_test));

  if (!do_test) {
    DEBUG_PRINTF(("<actuator.c> actuate_devices: set actuate test complete to FALSE\n"));
    set_actuate_test_complete(0, 0);
    set_actuate_test_complete(1, 0);
  }

  /*@ loop invariant 0 <= d && d <= NDEV;
    @ loop assigns d, err, core.test.test_device_done[0..2], core.test.test_device_result[0..2];
    */
  for (uint8_t d = 0; d < NDEV; ++d)
    /*$ inv
      0u8 <= d && d <= NDEV();
      take cii = Owned<struct core_state>(&core);
      core_state_ok(cii);
      take dalinv = Owned<uint8_t[2][2]>(&device_actuation_logic);
      take asinv = Owned<uint8_t[4]>(&actuator_state);
    $*/
  {
    uint8_t votes = 0;
    uint8_t test_votes = 0;

    /*@ loop invariant 0 <= l && l <= NVOTE_LOGIC;
      @ loop assigns l, err, test_votes, votes;
    */
    for (uint8_t l = 0; l < NVOTE_LOGIC; ++l)
      /*$ inv
        0u8 <= l && l <= NVOTE_LOGIC();
        0u8 <= d && d < NDEV();
        take ciii = Owned<struct core_state>(&core);
        core_state_ok(ciii);
        take dalinv2 = Owned<uint8_t[2][2]>(&device_actuation_logic);
        take asinv2 = Owned<uint8_t[4]>(&actuator_state);
      $*/
    {
      uint8_t this_vote = 0;
      err   |= get_actuation_state(l, d, &this_vote);
      if (do_test && l == get_test_actuation_unit())
        test_votes |= ((this_vote & 0x1) << d);
      else if (VALID(this_vote))
        votes |= (this_vote << d);
    }

    if (do_test && d == get_test_device()) {
      if (!is_actuate_test_complete(get_test_device())) {
        DEBUG_PRINTF(("<actuator.c> actuate_devices: set_actuate_test_result(0x%X, ActuateActuator(0x%X))\n",
                d, test_votes));
        set_actuate_test_result(d, ActuateActuator(test_votes));
        set_actuate_test_complete(d, 1);
      }
    }

    // Call out to actuation policy
    DEBUG_PRINTF(("<actuator.c> actuate_devices: Call out to actuation policy, set_actuate_device(0x%X, ActuateActuator(0x%X))\n",
                d, votes));
    err |= set_actuate_device(d, ActuateActuator(votes));
  }

  return err;
}
