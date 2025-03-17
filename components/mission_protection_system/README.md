# Mission Protection System (MPS)

- [Mission Protection System (MPS)](#mission-protection-system-mps)
  - [Requirements](#requirements)
    - [Architectural Requirements](#architectural-requirements)
    - [Functional Requirements](#functional-requirements)
    - [Testing Requirements](#testing-requirements)
  - [Porting Notes](#porting-notes)


An engine protection system, that is redundant, measures engine temperature, and fuel pressure, and shuts down the engine if unsafe values are detected.

The system is connected to two temperature sensors and two fuel pressure sensors. The system has a control interface that allows the user to enter the maintenance mode, and adjust setpoints and trip channels. This control interface is available via a serial console (UART), and as such can be accessed only when the platform is not in operation (imagine the UART port being hidden behind a body panel).

## Requirements

### Architectural Requirements

* **TA2-REQ-40: Four instrumentation channels**
  * MPS shall have four redundant divisions of instrumentation, each containing identical designs, with two instrumentation channels (Fuel Pressure and Temperature), each channel containing:
    * A. Sensor
    * B. Data acquisition and filtering
    * C. Setpoint comparison for trip generation
    * D. Trip output signal generation
* **TA2-REQ-41: Actuation logic**
  * MPS shall have two trains of actuation logic, each containing identical designs:
    * A. Two-out-of-four coincidence logic of like trip signals
    * B. Logic to actuate a first device based on an OR of two instrumentation coincidence signals
    * C. Logic to actuate a second device based on the remaining instrumentation coincidence signal

### Functional Requirements

* **TA2-REQ-27: High pressure trip**
  * MPS shall Trip on high pressure (sensor to actuation)
* **TA2-REQ-28: High temperature trip**
  * MPS shall Trip on high temperature (sensor to actuation)
* **TA2-REQ-29: Voting logic**
  * MPS shall Vote on like trips using two-out-of-four coincidence
* **TA2-REQ-30: Automatic actuation**
  * MPS shall Automatically actuate devices
* **TA2-REQ-31: Manual actuation**
  * MPS shall Manually actuate each device upon receiving a user command
  * **Comment:** This command was received over UART, after the second change event the command is received over a socket.
* **TA2-REQ-32: Operating modes**
  * MPS shall Select mutually exclusive maintenance and normal operating modes on a per division basis
* **TA2-REQ-33: Setpoint adjustment**
  * MPS shall Perform setpoint adjustment in maintenance mode
* **TA2-REQ-34: Maintenance mode bypass**
  * MPS shall Configure the system in maintenance mode to bypass an instrument channel (prevent it from generating a corresponding active trip output)
* **TA2-REQ-35: Maintenance mode forced trip**
  * MPS shall Configure the system in maintenance mode to force an instrument channel to an active trip output state
* **TA2-REQ-36: Variables displayed**
  * MPS shall Display pressure, and temperature
* **TA2-REQ-37: Trip state displayed**
  * MPS shall Display each trip output signal state
* **TA2-REQ-38: Bypass indication display**
  * MPS shall Display indication of each channel in bypass
* **TA2-REQ-39: Periodic self-test**
  * MPS shall run Periodic continual self-test of safety signal path (e.g., overlapping from sensor input to actuation output)

### Testing Requirements

Traditionally, this section would be called *Verification Requirements*, but in the context of VERSE *verification* means *providing a formal proof*, thus *testing* is a more appropriate label.

* **TA2-REQ-21: Completeness and consistency**
  * MPS shall demonstrate the Completeness and consistency of requirements
  * **Comment:** Achieved via formalization of the requirements in FRET (see the HARDENS assurance case) and via test cases.
* **TA2-REQ-22: Instrumentation independence**
  * MPS shall demonstrate Independence among the four divisions of instrumentation (inability for the behavior of one division to interfere or adversely affect the performance of another)
* **TA2-REQ-23: Instrumentation independence within a division**
  * MPS shall demonstrate Independence among the two instrumentation channels within a division (inability for the behavior of one channel to interfere or adversely affect the performance of another)
* **TA2-REQ-24: Actuation logic independence**
  * MPS shall demonstrate Independence among the two trains of actuation logic (inability for the behavior of one train to interfere or adversely affect the performance another)
* **TA2-REQ-25: Actuation on coincidence vote or manual action**
  * MPS shall demonstrate Completion of actuation whenever coincidence logic is satisfied or manual actuation is initiated
* **TA2-REQ-26: Self test and trip independence**
  * MPS shall demonstrate Independence between periodic self-test functions and trip functions (inability for the behavior of the self-testing to interfere or adversely affect the trip functions)

## Porting Notes

The MPS is being adapted from a high-assurance model reactor control system (HARDENS) which includes converting the Frama-C ACSL specifications to CN specifications. 
Many C features are not yet supported by CN, the ones that most seriously affect the MPS are lack of variadic functions (all logging printfs) and lack of unions (the instrumentation_command struct).

ACSL constructs mostly have direct analogs in CN:

- `requires` and `ensures` are the same
- `\valid` should become `Owned`, not `Block`, it requires reading and writing ability.
- `assigns` means the value in that location can change. Other locations can be written as long as they are restored before the function exits. It doesn't make any demand on the value in the location, so it is taking and returning an `Owned`.
- `<==>` between predicates can be replaced with `==`, it is equivalence on booleans instead of predicates.
