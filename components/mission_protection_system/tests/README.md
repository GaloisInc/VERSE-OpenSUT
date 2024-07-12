# End-to-End Runtime Verification for MPS

This directory contains the drivers and testcases that implement test
scenarios defined in [the Lando specification](../specs/test_scenarios.lando).

Each scenario is a template, potentially parameterized by a set of
variables, as outlined below.

To run all the tests, just run:

``` sh
make
```

Some tests have a large number of cases. As the implementation and
tests are symmetric, you can do a quick sanity run by setting the
`QUICK` environment variable, i.e.:

``` sh
QUICK=1 make
```

Individual tests can be run (and debugged) by using the `test.py` script:

``` sh
MPS_BIN=path/to/mps/binary ./test.py <path/to/scenario> [path/to/scenario.cases]
```

Defining the `MPS_DEBUG` envrionment variable will cause the tester to
print out debug output, including which commands are sent to the
binary and which output is being checked.

## Scenario format

A scenario is a file whose structure is:

  1. An optional list of parameters
  2. A sequence of commands

A command is either a MPS command (such as "M" for setting maintenance
mode) or a regular expression preceeded by the character `?`.

Tests proceed by executing commands one by one. Regular expressions
are tested against the output produced thus far. A test fails if a
regular expression fails to match after a number of retries.

For example, the scenario:

    {T}
    V 0 0 {T}
    V 1 0 {T}

    ?#I 0.*

has one parameter `T`. Next the commands `V 0 0 {T}` and `V 1 0 {T}`
are MPS commands that simulate a temperature sensor reading of the
_value_ of the parameter `T` in both sensors. Finally, the regular
expression at the bottom simply tests that the string `#I 0` is
eventually printed to the console.

## "Skipped" tests

This directory includes a set of "skipped" tests. Actually these are
scenarios that may _refine_ those already under `scenarios`. Some of
these refinements require very sophisticated regular expressions to
match against, and hence we do not currently use them for testing.

For example, `exceptional_5{a,b,c,d,e}` describe scenarios where a
demultiplexor fails. One way to check this condition is to look for
the warning that two sensors differ by too large of a value. Another
test, that is not quite equivalent, would be look for a UI state in
which at least two sensor values differ: clearly this is quite a
complicated regular expression.


# Running Tests under `vm_runner`

This section describes how to run the test suite against an instance of MPS
that is running under a guest VM managed by the OpenSUT `vm_runner`.

First, cross-compile MPS for aarch64 in the appropriate configuration:

```sh
# In the mission_protection_system/src/ directory:
make CONFIG=no_self_test TARGET=aarch64
```

This will produce an aarch64 `mps.no_self_test.aarch64` binary.  On Debian, the
necessary aarch64 toolchain can be installed from the `g++-aarch64-linux-gnu`
package.

Then, in the `vm_runner` directory, prepare host and guest application images
for running MPS:

```sh
# In the vm_runner/ directory:
bash tests/mps/build_image.sh
```

This copies the aarch64 `mps` binary produced above into the images.

Start the VMs and MPS by running:

```sh
# In the vm_runner/ directory:
cargo run -- tests/mps/base_nested.toml
```

This will start a host VM, a guest VM, and MPS inside the guest VM.  It will
print various Linux boot messages, followed by a line like this:

```
[   65.044425] opensut_boot[302]: [   39.737218] opensut_boot[305]: Starting mps
```

At this point, MPS is running inside the VM.

For manual testing, you can connect to MPS via `socat`:

```sh
# In the vm_runner/ directory:
socat - unix:./serial.socket
```

This should display the usual MPS status screen and accept commands as normal.
Press ^C to disconnect (MPS will continue running).  To restart MPS and reset
it to its initial state, enter the `R` (reset) command.

In this setup, `serial.socket` on the base system is connected to an emulated
UART in the host VM, which is forwarded to an emulated UART in the guest VM,
and MPS communicates over that emulated UART.  See `vm_runner/tests/mps*.toml`
for details.

The MPS test suite can now be run against `serial.socket`, which allows testing
MPS as it runs inside the VM.  In the MPS `tests/` subdirectory, run the suite
with the appropriate environment variables set:

```sh
# In the mission_protection_system/tests/ directory:
MPS_SOCKET=/path/to/vm_runner/serial.socket python3 run_all.py
```

All tests should pass as normal in this configuration.


# License

   Copyright 2021, 2022, 2023 Galois, Inc.

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
