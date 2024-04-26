# Mission Protection System (MPS)

An engine protection system, that is redundant, measures engine temperature, and fuel pressure, and shuts down the engine if unsafe values are detected.

The system is connected to two temperature sensors and two fuel pressure sensors. The system has a control interface that allows the user to enter the maintenance mode, and adjust setpoints and trip channels. This control interface is available via a serial console (UART), and as such can be accessed only when the platform is not in operation (imagine the UART port being hidden behind a body panel).

## Requirements

### Architectural Requirements

* A.1 MPS shall have four redundant divisions of instrumentation, each containing identical designs:
    * A.1.1 Two instrumentation channels (Fuel Pressure and Temperature), each channel containing:
      * Sensor
      * Data acquisition and filtering
      * Setpoint comparison for trip generation
      * Trip output signal generation
* A.2 MPS shall have two trains of actuation logic, each containing identical designs:
    * A.2.1 Two-out-of-four coincidence logic of like trip signals
    * A.2.2 Logic to actuate a first device based on an OR of two instrumentation coincidence signals
    * A.2.3 Logic to actuate a second device based on the remaining instrumentation coincidence signal

### Functional Requirements

* F.1 MPS shall Trip on high pressure (sensor to actuation)
* F.2 MPS shall Trip on high temperature (sensor to actuation)
* F.3 MPS shall Vote on like trips using two-out-of-four coincidence
* F.4 MPS shall Automatically actuate devices
* F.5 MPS shall Manually actuate each device upon receiving a user command
* F.5 MPS shall Select mutually exclusive maintenance and normal operating modes on a per division basis
* F.6 MPS shall Perform setpoint adjustment in maintenance mode
* F.7 MPS shall Configure the system in maintenance mode to bypass an instrument channel (prevent it from generating a corresponding active trip output)
* F.8 MPS shall Configure the system in maintenance mode to force an instrument channel to an active trip output state
* F.9 MPS shall Display pressure, and temperature
* F.10 MPS shall Display each trip output signal state
* F.11 MPS shall Display indication of each channel in bypass
* F.12 MPS shall run Periodic continual self-test of safety signal path (e.g., overlapping from sensor input to actuation output)

### Verification Requirements

* V.1 MPS shall demonstrate the Completeness and consistency of requirements
* V.2 MPS shall demonstrate Independence among the four divisions of instrumentation (inability for the behavior of one division to interfere or adversely affect the performance of another)
* V.3 MPS shall demonstrate Independence among the two instrumentation channels within a division (inability for the behavior of one channel to interfere or adversely affect the performance of another)
* V.4 MPS shall demonstrate Independence among the two trains of actuation logic (inability for the behavior of one train to interfere or adversely affect the performance another)
* V.5 MPS shall demonstrate Completion of actuation whenever coincidence logic is satisfied or manual actuation is initiated
* V.6 MPS shall demonstrate Independence between periodic self-test functions and trip functions (inability for the behavior of the self-testing to interfere or adversely affect the trip functions)
