This document contains all OpenSUT requirements, and was created with the help of `StrictDocs <https://strictdoc.readthedocs.io/en/stable/>`_. For text formatting, the reStructuredText markup syntax is supported, see `the RST cheatsheet <https://bashtage.github.io/sphinx-material/rst-cheatsheet/rst-cheatsheet.html>`_.

If you are new to requirement writing, we recommend reading first the *21 Top Engineering Tips for writing an exceptionally clear requirements document* from QRA (available as `PDF here <https://github.com/GaloisInc/VERSE-OpenSUT/blob/main/docs/QRA_Clear_Requirements.pdf>`_),
then refer to *NASA's checklist for writing good requirements* `here <https://www.nasa.gov/reference/appendix-c-how-to-write-a-good-requirement/>`_.

The OpenSUT requirements are split into different sections and subsections. Each requirement has its section number (e.g. *4.1.1.2 Actuation Logic*) and its Unique Identifier (UID). The section number is used only in this document, the UID guaranteed to be globally unique. On top of UID, we also use StrictDocs' `MID <https://strictdoc.readthedocs.io/en/stable/strictdoc_01_user_guide.html#machine-identifiers-mid>`_. For requirement tracing and coverage measurement, we use primarily the UID.

Requirements that use the word *shall* are binding and must be satisfied, while requirements using the word *should* are non-binding, and can be considered optional or nice-to-have. A *rationale* is provided when appropriate for a given requirement.

.. _SECTION-OR-SoW-Requirements:

SoW Requirements
================

Derived from the Statement of Work for the purpose of tracing the individual tasks and issues back to the SoW.

.. _SECTION-OR-OpenSUT-Platform:

OpenSUT Platform
----------------

Task **TA2.1.1**

.. _TA2-REQ-42:

Task TA2.1.1.A
~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-42
    * - **STATUS:**
      - Completed

Develop the Open SUT primarily using existing components and specifications, including:

* Flight Controller
* AutoPilot
* Secure boot
* Mission Key Management
* Mission Protection System components.


Port a subset of OpenSUT components to run in a pKVM guest VM.

.. _TA2-REQ-44:

Task TA2.1.1.B
~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-44
    * - **STATUS:**
      - Completed

Specify entire OpenSUT architecture with SysML, and AADL.

.. _TA2-REQ-45:

Task TA2.1.1.C
~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-45
    * - **STATUS:**
      - Completed

Develop VERSE Toolchain specifications for components with rich code-level specifications.

.. _SECTION-OR-Apply-VERSE-to-Open-SUT:

Apply VERSE to Open SUT
-----------------------

Task **TA2.1.2**

.. _TA2-REQ-46:

Task TA2.1.2.A
~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-46
    * - **STATUS:**
      - Completed

Build assurance case for the Open SUT.

.. _TA2-REQ-47:

Task TA2.1.2.B
~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-47
    * - **STATUS:**
      - Completed

Apply Verse Development Environment (VDE) to provide qualitative and quantitative feedback.

.. _TA2-REQ-48:

Task TA2.1.2.C
~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-48
    * - **TAGS:**
      - Completed

Define system deltas for program evolution and evaluation.

.. _TA2-REQ-49:

Task TA2.1.2.D
~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-49
    * - **TAGS:**
      - Completed

Support two Phase 1 continuous integration events.

.. _SECTION-OR-Code-requirements:

OpenSUT Code Requirements
=========================

In this section we list requirements about the overall OpenSUT code, its structure, coverage and format.

.. _TA2-REQ-16:

No undefined behavior
---------------------

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-16
    * - **STATUS:**
      - Completed

OpenSUT shall not contain any C code with undefined behavior, as defined by Cerberus semantics.

**RATIONALE:**

An example of undefined behavior include division by zero, out of bounds array access, integer overflow and null pointer dereference.

**COMMENT:**

This is only valid for the verified application code.

**Children:**

- ``[TA2-REQ-51]`` :ref:`TA2-REQ-51`

.. _TA2-REQ-17:

MISRA-C compliant code
----------------------

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-17

OpenSUT application code should be MISRA-C compliant.

**RATIONALE:**

It is acceptable to choose only a subset of MISRA-C, such that it is supported by open-source tools, or regular IDEs (such as `CLion <https://youtrack.jetbrains.com/articles/CPP-A-191430682>`_).

.. _SECTION-OR-OpenSUT-Scenario-Requirements:

OpenSUT Scenario Requirements
=============================

Requirements related to each OpenSUT scenarios.

.. _SECTION-OR-Boot-OpenSUT-to-a-known-initial-state:

Boot OpenSUT to a known initial state
-------------------------------------

In this scenario, one or more components of OpenSUT boot using SHAVE Trusted Boot. It means that the application code is measured, hashed, and compared against an expected measure. Only if these values match, the application code is started and the measure is stored in the memory. If they don't match, an error is thrown, the boot is aborted and an error message is possibly sent and logged. If the attestation of each securely booted component passes, the system will be in a known initial state, fully provisioned. Measured boot ensures that only the expected code is running on OpenSUT.

The code is measured either with SHA256 or with quantum safe eXtended Merkle Signature Scheme (XMSS).

For the purpose of this scenario, we assume that each host computer contains a root of trust, a trusted boot that can bring up the hypervisor. In other words, we assume the host OS to be trusted (see the Threat model). Because hardware root of trust, trusted boot and attestation are all complex topics, only the application code will be attested in this scenario.

.. _TA2-REQ-20:

Signature of application code image
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-20
    * - **STATUS:**
      - Completed

Each application disk image shall contain a digital signature that can be verified by the secure boot.

**Parents:**

- ``[TA2-REQ-19]`` :ref:`TA2-REQ-19`

**Children:**

- ``[TA2-REQ-59]`` :ref:`TA2-REQ-59`

.. _TA2-REQ-19:

Secure booting only the application code
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-19
    * - **STATUS:**
      - Completed

Secure boot shall be used to boot only the application code, and only on a subset of OpenSUT components.

**RATIONALE:**

This simplification is consistent with out threat model. Demonstrating Secure Boot only on a subset of components is sufficient.

**Parents:**

- ``[TA2-REQ-18]`` :ref:`TA2-REQ-18`

**Children:**

- ``[TA2-REQ-20]`` :ref:`TA2-REQ-20`
- ``[TA2-REQ-54]`` :ref:`TA2-REQ-54`

.. _TA2-REQ-18:

Explicit assumptions
~~~~~~~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-18
    * - **STATUS:**
      - Completed

In the provided documentation, explicitly list the assumptions and limitations of OpenSUT, such as:

* this is a contrived example
* true secure boot is not possible unless a *chain of trust* going all the way down to *Hardware Root of Trust* is maintained
* in real system a true *Hardware Security Module* (HSM) - such as the one developed on SEASHIP needs to be deployed on each Host computer, and shared with the guests

**Children:**

- ``[TA2-REQ-19]`` :ref:`TA2-REQ-19`

.. _SECTION-OR-Component-Requirements:

Component Requirements
======================

Component specific requirements are located in this section

.. _SECTION-OR-Mission-Protection-System-Requirements:

Mission Protection System (MPS) Requirements
--------------------------------------------

An engine protection system, that is redundant, measures engine temperature, and fuel pressure, and shuts down the engine if unsafe values are detected.

The system is connected to two temperature sensors and two fuel pressure sensors. The system has a control interface that allows the user to enter the maintenance mode, and adjust setpoints and trip channels. This control interface is available via a serial console (UART), and as such can be accessed only when the platform is not in operation (imagine the UART port being hidden behind a body panel).

.. _SECTION-OR-MPS-Architectural-Requirements:

MPS Architectural Requirements
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. _TA2-REQ-40:

Four instrumentation channels
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-40
    * - **STATUS:**
      - Completed

MPS shall have four redundant divisions of instrumentation, each containing identical designs, with two instrumentation channels (Fuel Pressure and Temperature), each channel containing:

A. Sensor
B. Data acquisition and filtering
C. Setpoint comparison for trip generation
D. Trip output signal generation

.. _TA2-REQ-41:

Actuation logic
^^^^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-41
    * - **STATUS:**
      - Completed

MPS shall have two trains of actuation logic, each containing identical designs:

A. Two-out-of-four coincidence logic of like trip signals
B. Logic to actuate a first device based on an OR of two instrumentation coincidence signals
C. Logic to actuate a second device based on the remaining instrumentation coincidence signal

.. _SECTION-OR-MPS-Functional-Requirements:

MPS Functional Requirements
~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. _TA2-REQ-27:

High pressure trip
^^^^^^^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-27
    * - **STATUS:**
      - Completed

MPS shall Trip on high fuel pressure (sensor to actuation)

.. _TA2-REQ-28:

High temperature trip
^^^^^^^^^^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-28
    * - **STATUS:**
      - Completed

MPS shall Trip on high temperature (sensor to actuation)

.. _TA2-REQ-29:

Voting logic
^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-29
    * - **STATUS:**
      - Completed

MPS shall Vote on like trips using two-out-of-four coincidence

.. _TA2-REQ-30:

Automatic actuation
^^^^^^^^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-30
    * - **TAGS:**
      - Completed

MPS shall Automatically actuate devices.

.. _TA2-REQ-31:

Manual actuation
^^^^^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-31
    * - **STATUS:**
      - Completed

MPS shall Manually actuate each device upon receiving a user command.

**COMMENT:**

This command was received over UART, after the second change event the command is received over a socket.

.. _TA2-REQ-32:

Operating modes
^^^^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-32
    * - **STATUS:**
      - Completed

MPS shall Select mutually exclusive maintenance and normal operating modes on a per division basis.

.. _TA2-REQ-33:

Setpoint adjustment
^^^^^^^^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-33
    * - **STATUS:**
      - Completed

MPS shall Perform setpoint adjustment in maintenance mode.

.. _TA2-REQ-34:

Maintenance mode bypass
^^^^^^^^^^^^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-34
    * - **STATUS:**
      - Completed

MPS shall Configure the system in maintenance mode to bypass an instrument channel (prevent it from generating a corresponding active trip output).

.. _TA2-REQ-35:

Maintenance mode forced trip
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-35
    * - **STATUS:**
      - Completed

MPS shall Configure the system in maintenance mode to force an instrument channel to an active trip output state.

.. _TA2-REQ-36:

Variables displayed
^^^^^^^^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-36
    * - **STATUS:**
      - Completed

MPS shall Display fuel pressure, and engine temperature.

.. _TA2-REQ-37:

Trip state displayed
^^^^^^^^^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-37
    * - **STATUS:**
      - Completed

MPS shall Display each trip output signal state.

.. _TA2-REQ-38:

Bypass indication display
^^^^^^^^^^^^^^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-38
    * - **STATUS:**
      - Completed

MPS shall Display indication of each channel in bypass.

.. _TA2-REQ-39:

Periodic self-test
^^^^^^^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-39
    * - **STATUS:**
      - Completed

MPS shall run Periodic continual self-test of safety signal path (e.g., overlapping from sensor input to actuation output).

.. _SECTION-OR-MPS-Testing-Requirements:

MPS Testing Requirements
~~~~~~~~~~~~~~~~~~~~~~~~

Traditionally, this section would be called *Verification Requirements*, but in the context of VERSE *verification* means *providing a formal proof*, thus *testing* is a more appropriate label.

.. _TA2-REQ-21:

Completeness and consistency
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-21
    * - **STATUS:**
      - Completed

MPS shall demonstrate the Completeness and consistency of requirements

**COMMENT:**

Achieved via formalization of the requirements in FRET (see the HARDENS assurance case) and via test cases.

.. _TA2-REQ-22:

Instrumentation independence
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-22
    * - **STATUS:**
      - Completed

MPS shall demonstrate Independence among the four divisions of instrumentation (inability for the behavior of one division to interfere or adversely affect the performance of another)

.. _TA2-REQ-23:

Instrumentation independence within a division
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-23
    * - **STATUS:**
      - Completed

MPS shall demonstrate Independence among the two instrumentation channels within a division (inability for the behavior of one channel to interfere or adversely affect the performance of another)

.. _TA2-REQ-24:

Actuation logic independence
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-24
    * - **STATUS:**
      - Completed

MPS shall demonstrate Independence among the two trains of actuation logic (inability for the behavior of one train to interfere or adversely affect the performance another)

.. _TA2-REQ-25:

Actuation on coincidence vote or manual action
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-25
    * - **STATUS:**
      - Completed

MPS shall demonstrate Completion of actuation whenever coincidence logic is satisfied or manual actuation is initiated.

.. _TA2-REQ-26:

Self test and trip independence
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-26
    * - **STATUS:**
      - Completed

MPS shall demonstrate Independence between periodic self-test functions and trip functions (inability for the behavior of the self-testing to interfere or adversely affect the trip functions)

.. _SECTION-OR-Secure-Boot-Requirements:

Secure Boot Requirements
------------------------

A system boot where aspects of the hardware and firmware are measured and compared against known good values to verify their integrity and thus their trustworthiness.

.. _SECTION-OR-Secure-Boot-Functional-Requirements:

Secure Boot Functional Requirements
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. _TA2-REQ-54:

Known initial state
^^^^^^^^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-54
    * - **STATUS:**
      - Completed

The Secure Boot shall bring a given component to a known initial state.

**Parents:**

- ``[TA2-REQ-19]`` :ref:`TA2-REQ-19`

.. _TA2-REQ-65:

Code attestation
^^^^^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-65
    * - **STATUS:**
      - Completed

Secure boot shall provide attestation for the application code.

.. _TA2-REQ-55:

Boot debug information
^^^^^^^^^^^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-55
    * - **STATUS:**
      - Completed

The Secure Boot shall print information to the console/serial port for debugging purposes.

.. _TA2-REQ-56:

Secure boot termination
^^^^^^^^^^^^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-56
    * - **STATUS:**
      - Deferred

The Secure Boot shall always terminate.

**COMMENT:**

CN cannot currently prove termination properties

.. _TA2-REQ-57:

Launch application or terminate
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-57
    * - **STATUS:**
      - Completed

The Secure boot shall either launch the application, or if an error occurs, log the error and terminate.

.. _TA2-REQ-58:

Clear memory
^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-58
    * - **STATUS:**
      - Deferred

The Secure boot shall erase all RAM containing the secure boot data before a handoff to the application code.

**RATIONALE:**

This prevents accidental leakage of private information to the potentially compromised application, such as private keys or attestation information.

**COMMENT:**

Memory erasing is difficult to achieve for a linux process. This requirement will be relevant for embedded scenarios.

.. _SECTION-OR-Secure-Boot-Security-Requirements:

Secure Boot Security Requirements
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. _TA2-REQ-60:

Measurement algorithm
^^^^^^^^^^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-60
    * - **STATUS:**
      - Completed

The Secure Boot shall use high assurance implementation of cryptographic algorithms.

**RATIONALE:**

For example an implementation that has been formally verified against a "golden" specification, or an implementation automatically generated from such "golden specification".

.. _TA2-REQ-59:

Binary code measurement
^^^^^^^^^^^^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-59
    * - **STATUS:**
      - Completed

The Secure Boot shall measure the application binary and compare it against a stored good known value.

**Parents:**

- ``[TA2-REQ-20]`` :ref:`TA2-REQ-20`

.. _TA2-REQ-61:

Secure store of the hash measurement
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-61
    * - **STATUS:**
      - Deferred

The Secure Boot should store the measured values in a Trusted Platform Module or other secure memory storage.

**RATIONALE:**

Normally this requirement would be binding ("shall"), but given the scope of our threat model, this requirement is optional ("should").

**COMMENT:**

No TPM available.

.. _TA2-REQ-62:

Abort on mismatched measurements
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-62
    * - **STATUS:**
      - Completed

The Secure Boot shall abort the boot process and throw an error, if the expected and measured values do not match.

.. _TA2-REQ-63:

Secure Boot stored in read-only memory
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-63
    * - **STATUS:**
      - Deferred

The Secure Boot executable shall be stored in a read only memory, or with read-only permissions.

**RATIONALE:**

This avoids possible modifications to the secure boot executable.

**COMMENT:**

Not implemented, as for simpler execution we run the secure boot and the application code in the same userspace.

.. _TA2-REQ-64:

Do not compare measurements if expected value is not provided
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-64
    * - **STATUS:**
      - Completed

If no expected value of the application binary is provided, the secure boot shall only perform a measurement, save it, and launch the application.

**RATIONALE:**

If an application is not signed, the secure boot measurement comparison is disabled.

.. _SECTION-OR-MKM-Requireme ts:

Mission Key Management Requirements
-----------------------------------

Mission Key Management (MKM) processes key requests and distributes keys to other components. Any component can connect to the MKM, request a key, and attest to the code that it's running; the MKM will then send the key if allowed by the MKM's built-in policy.

We require the MKM to implement the following protocol:

1. The client connects to the MKM over TCP.
2. The client component sends a key ID (1 byte), indicating which key it is
   requesting.
3. The MKM sends a random nonce (16 bytes).
4. The client obtains an attestation matching the challenge (by communicating
   with its trusted boot daemon) and sends the attestation (64 bytes).
5. If the attestation is valid and MKM policy allows the component to receive
   the requested key, the MKM sends the key (32 bytes).

If an error occurs, such as an invalid attestation or a policy violation, the
MKM simply closes the connection without sending the key.

Since all messages have a fixed size and occur in a fixed order, the protocol
does not use any headers or delimiters for messages.

The MKM server listens on localhost (127.0.0.1) port 6000 by default.  To
change this, set the `MKM_BIND_ADDR` and/or `MKM_PORT` environment variables.
For example, `MKM_BIND_ADDR=0.0.0.0 MKM_PORT=6001 ./mkm config.bin` will cause
it to listen on port 6001 on all network interfaces.

.. _TA2-REQ-66:

Close connection on error
~~~~~~~~~~~~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-66

If an error occurs at any time during the key exchange protocol, such as an invalid attestation or a policy violation, the MKM shall close the connection without sending the key.

.. _TA2-REQ-67:

No headers or delimiters for messages
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-67

All MKM messages shall have a fixed size and occur in a fixed order, and the protocol shall not use any headers or delimiters for messages.

.. _TA2-REQ-68:

TCP connection
~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-68

The client shall connect to the MKM over TCP via a socket.

.. _TA2-REQ-69:

Wait for key ID
~~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-69

While the MKM is ready to receive connections, a client component shall send a key ID (1 byte), indicating which key it is requesting.

.. _TA2-REQ-70:

Send challenge
~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-70

When a key ID is received from a client, the MKM shall send a random nonce (16 bytes) in return.

.. _TA2-REQ-71:

Valid key ID
~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-71

The MKM shall process only a valid key ID.

.. _TA2-REQ-72:

Calculate attestation
~~~~~~~~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-72

Once the client receives an attestation challenge (nonce) from the MKM, the client shall compute the response by communicating with its trusted boot daemon and send the response back to the MKM.

.. _TA2-REQ-73:

Challenge response format
~~~~~~~~~~~~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-73

The challenge response shall be computed by concatenating the current measured value (matching the expected hash of the binary) with the received nonce, and then computing HMAC of the concatenated value using a secret key. The resulting response is 64 bytes long.

.. _TA2-REQ-74:

Secure boot secret key
~~~~~~~~~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-74

The secret key may be identical across different components, so as to simplify the key management. This key is known at build time to the MKM.

**RATIONALE:**

In real world, secure boot would store unique and shared keys in a Hardware Root of Trust (HROT) and the decision whether to use unique or shared keys would be based on the actual threat model. In either way, the MKM must know the key to validate the attestation response.

.. _TA2-REQ-75:

Receive response
~~~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-75

Once the MKM receives the attestation response, it shall check its validity. A valid attestation is calculated as described in TA2-REQ-73.

.. _TA2-REQ-76:

Send key
~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-76

If the received response is valid, the MKM shall send back to the client the associated mission key and terminate the connection.

.. _TA2-REQ-77:

Key format
~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-77

The mission key is 32-bytes long symmetric AES key.

.. _SECTION-OR-Logging-Component-Requirements:

Logging Component Requirements
------------------------------

.. _TA2-REQ-78:

Save telemetry to disk
~~~~~~~~~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-78

The logging component shall connect to the secondary autopilot telemetry port and record some or all telemetry values to disk.

.. _TA2-REQ-79:

Read from a socket
~~~~~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-79

The logging component shall read MAVlink messages from a socket

.. _TA2-REQ-80:

Log file format
~~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-80

Logs shall be saved in text format, with a timestamp on each line.

.. _TA2-REQ-81:

Debug print
~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-81

Logs may be printed to stdout for debugging purposes.

.. _TA2-REQ-82:

Encrypted storage
~~~~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-82

Logs shall be encrypted by storing them on an encrypted filesystem.

.. _TA2-REQ-83:

Encryption keys
~~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-83

The key for the encrypted filesystem shall be obtained from the Mission Key Management component.

.. _TA2-REQ-84:

Filesystem initialization
~~~~~~~~~~~~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-84

The filesystem shall be initialized on first use.

.. _SECTION-OR-VERSE-Toolchain-Requirements:

VERSE Toolchain Requirements
============================

VERSE Toolchain specific requirements, driven by the TA2 needs.

.. _SECTION-OR-Robustness-requirements:

VERSE Toolchain Usability Requirements
--------------------------------------

Requirements related to the user experience with VERSE Toolchain in general.

.. _TA2-REQ-1:

No crashing
~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-1
    * - **STATUS:**
      - Deferred

VERSE Toolchain shall not crash on arbitrary input. Instead, an error message shall be produced.

**RATIONALE:**

Even if a specification is incorrect, or the input file is not a valid C code, VERSE Toolchain should gracefully exit.

**COMMENT:**

Guaranteeing this requirement for all possible inputs was beyond the scope of the TA1 team's effort.

.. _TA2-REQ-2:

Special delimiters
~~~~~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-2
    * - **STATUS:**
      - Completed

VERSE Toolchain should support multiple special delimiters, such as `//@` or `/*@` or `/**@`. Which special delimiter should be used can be either configurable, or VERSE Toolchain should support all of them at the same time (see TA2-REQ-15).

**RATIONALE:**

In some codebases, VERSE Toolchain specs need to co-exist with existing specifications (such as Frama-C ACSL), such that adding VERSE Toolchain specs does not break the existing proofs.

**Parents:**

- ``[TA2-REQ-7]`` :ref:`TA2-REQ-7`

.. _TA2-REQ-7:

Multiple specification languages
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-7
    * - **STATUS:**
      - Completed

VERSE Toolchain shall run on codebases with multiple specification languages, such as Frama-C, SAW, and Cryptol.

**RATIONALE:**

High assurance code might contain multiple different spec languages. For VERSE program, we expect that only Frama-C ACSL specifications will exist directly in the C source code. Other specs, such as SAW and Cryptol, do not change the C code directly.

**Children:**

- ``[TA2-REQ-2]`` :ref:`TA2-REQ-2`
- ``[TA2-REQ-8]`` :ref:`TA2-REQ-8`

.. _TA2-REQ-8:

Continuity of existing proofs
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-8
    * - **STATUS:**
      - Completed

Adding VERSE Toolchain specs to a codebase shall not break existing proofs about such codebase.

**RATIONALE:**

For example, adding VERSE Toolchain specs into an existing high assurance codebase shall not break the existing Frama-C proofs

**COMMENT:**

We run both Frama-C and CN proofs in the CI

**Parents:**

- ``[TA2-REQ-7]`` :ref:`TA2-REQ-7`

.. _TA2-REQ-15:

Project specific VERSE Toolchain configuration
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-15
    * - **STATUS:**
      - Deferred

VERSE Toolchain shall support project specific configuration, in the form of a configuration file that will adjust how VERSE Toolchain behaves.

**RATIONALE:**

This is a top level requirement, further specified in the child requirements.

**COMMENT:**

Out of scope for P1

**Children:**

- ``[TA2-REQ-12]`` :ref:`TA2-REQ-12`
- ``[TA2-REQ-13]`` :ref:`TA2-REQ-13`
- ``[TA2-REQ-14]`` :ref:`TA2-REQ-14`

.. _TA2-REQ-52:

Code similarity
~~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-52
    * - **STATUS:**
      - Deferred

The code checked by VERSE Toolchain and the code compiled and deployed on the OpenSUT shall be identical.

**RATIONALE:**

If the code that can be checked by VERSE Toolchain is substantially different from the code that is compiled and deployed, errors in the production code might not be captured, leading to presence of bugs and vulnerabilities.

**COMMENT:**

While the code is fairly similar, there are still some workarounds needed for the verification to pass.

.. _SECTION-OR-Functional-Requirements:

VERSE Toolchain Functional Requirements
---------------------------------------

This section lists requirements on the functionality of VERSE Toolchain, and the features it provides.

.. _TA2-REQ-3:

Versioned releases
~~~~~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-3
    * - **STATUS:**
      - Completed

VERSE Toolchain shall provide versioned releases, such that running VERSE Toolchain with `-V` flag shall print out the version of the tool.

**COMMENT:**

CN prints the commit hash as a version.

.. _TA2-REQ-5:

Variadic functions
~~~~~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-5
    * - **STATUS:**
      - Deferred

VERSE Toolchain shall support reasoning about variadic functions, such as `printf()`.

.. _TA2-REQ-4:

Packaged releases
~~~~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-4
    * - **STATUS:**
      - Completed

VERSE Toolchain shall provide packaged releases using industry standard mechanisms, such as docker, or debian packages.

**COMMENT:**

CN provides both Ubuntu and RedHat based docker images.

.. _TA2-REQ-6:

C Unions
~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-6
    * - **STATUS:**
      - Deferred

VERSE Toolchain shall support reasoning about C union types.

**RATIONALE:**

For example the MPS code relies heavily on unions, and such code needs to be supported.

**COMMENT:**

Planned for Phase 2

.. _TA2-REQ-9:

Nested types
~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-9
    * - **STATUS:**
      - Deferred

VERSE Toolchain shall support reasoning about structs composed of other structs.

**RATIONALE:**

For example VERSE Toolchain shall be able to reason about the following struct and prove that there is no undefined behavior and that any user defined specification holds for such a struct:

.. code-block:: c

    struct S {
        T1 S1;
        T2 *S2;
        T3 S3[];
    }

.. _TA2-REQ-53:

User defined type invariants
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-53
    * - **STATUS:**
      - Completed

VERSE Toolchain should support checking user defined type and data structure invariants. VERSE Toolchain should allow users to annotate types and data structures with invariants, such that the invariant is preserved at every instance of that type.

**RATIONALE:**

For example, the user wishes to prove that a pointer of particular type is never NULL. While NULL pointers are allowed under Cerberus C semantics, *dereferencing* a NULL pointer is an undefined behavior. Thus, a user defined invariant that a pointer shall never be NULL should be checkable by VERSE Toolchain.

Or given an array `T3 S3[];` the user wishes to prove that invariants about type T3 are valid for each element of array S3, and this is true for min and max size of S3, with min=0 and max some sensible default value (uint32_MAX?).

.. _TA2-REQ-10:

Specs in header of source file allowed
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-10
    * - **STATUS:**
      - Completed

VERSE Toolchain shall allow the user to write VERSE Toolchain specifications in either header (function declaration) or source file (function definition). If VERSE Toolchain specs are provided at both function declaration and function definition, VERSE Toolchain shall raise an error.

**RATIONALE:**

In some cases, writing specs in the header files is more ergonomic. In other cases, there might be no header files. The user shall have a choice that is the most suitable for a particular codebase. If accidentally the user writes multiple VERSE Toolchain specs for the same function (in the header and in the source file), VERSE Toolchain needs to throw an error an notify the user, as resolving which specs are valid is a complex problem.

.. _TA2-REQ-12:

Explicit assertion checking
~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-12
    * - **STATUS:**
      - Deferred

VERSE Toolchain shall have a configurable option to either ignore inline `assert()` statements, or to statically check them.

**RATIONALE:**

In some codebases, assertions are used only for selective runtime testing, so static checking might produce findings that are not interesting for the developers. The assertions are removed in the production code. Hence having the configurable option for VERSE Toolchain is important.

**COMMENT:**

Planned for Phase 2

**Parents:**

- ``[TA2-REQ-15]`` :ref:`TA2-REQ-15`

.. _TA2-REQ-13:

Well defined default behavior
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-13
    * - **STATUS:**
      - Deferred

If a function is not annotated with any VERSE Toolchain specifications, VERSE Toolchain shall explicitly state what are the default (implicit) `require`, `ensure` and `modify` clauses.

**RATIONALE:**

It needs to be stated whether by default each function requires and ensures nothing, or if there are some implicit assumptions, important for compositional reasoning. Same for modification - a sensible default behavior could be that a function without specs is assumed to modify everything. However, in that case compositional reasoning is not really possible, so having a configurable option here might be preferred.

The implicit `requires` might encompass e.g. a valid stack frame for the function.

**COMMENT:**

Planned in Phase 2, as a part of the documentation improvement.

**Parents:**

- ``[TA2-REQ-15]`` :ref:`TA2-REQ-15`

.. _TA2-REQ-14:

Annotation of pure functions
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-14
    * - **STATUS:**
      - Deferred

VERSE Toolchain shall have a configurable option to either assume that all functions are `pure` by default, or to require an explicit `pure` annotation.

**RATIONALE:**

Pure functions are side-effects free, and don't have any persistent static variables (see https://en.wikipedia.org/wiki/Pure_function). In some cases, explicitly stating which functions should be `pure` is easier, while in other codebases, it is reasonable to assume that the functions are `pure` by default. This should be configurable.

**Parents:**

- ``[TA2-REQ-15]`` :ref:`TA2-REQ-15`

.. _TA2-REQ-51:

Check for undefined behavior
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-51
    * - **STATUS:**
      - Completed

VERSE Toolchain shall check C code for undefined behavior as defined in Cerberus semantics, and raise an error when undefined behavior is found.

**RATIONALE:**

This is a base level functionality of VERSE Toolchain, as code with undefined behavior often leads to errors and unintended results.

**Parents:**

- ``[TA2-REQ-16]`` :ref:`TA2-REQ-16`

.. _SECTION-OR-Documentation-requirements:

VERSE Toolchain Documentation Requirements
------------------------------------------

Documentation of VERSE Toolchain, including manuals, tutorials, quick-start guides, code and document generation, and hints and error messages.

.. _TA2-REQ-11:

Generating code documentation with specs
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-11
    * - **STATUS:**
      - Deferred

TA1 tools shall generate source code documentation that includes VERSE Toolchain specification with VERSE Toolchain syntax highlighted.

**RATIONALE:**

Doxygen-like documentation with VERSE Toolchain specs included is ideal. It is important that the specs are not treated like comments, but are lifted and highlighted in the generated documents.

.. _TA2-REQ-50:

Code coverage measurement
~~~~~~~~~~~~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-50
    * - **STATUS:**
      - Deferred

VERSE Toolchain should provide means of measuring code coverage, and specifically reporting:

1) percentage or LOC of code/functions that have *any* specs
2) *any* code excluded from VERSE Toolchain checking (maybe hiding behind `#ifdef` or some other directive, excluding the code from being examined)
3) coverage based on types/classes of specifications (see the different classes we mentioned in the proposal)

**RATIONALE:**

See https://github.com/GaloisInc/VERSE-Toolchain/issues/93 for more details.
