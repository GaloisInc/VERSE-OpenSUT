================
OpenSUT Requirements
================


This document contains all OpenSUT requirements, and was created with the help of `StrictDocs <https://strictdoc.readthedocs.io/en/stable/>`_. For text formatting, the reStructuredText markup syntax is supported, see `the RST cheatsheet <https://bashtage.github.io/sphinx-material/rst-cheatsheet/rst-cheatsheet.html>`_.

.. _SECTION-OR-Code-requirements:

OpenSUT Code requirements
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

OpenSUT shall not contain any C code with undefined behavior, as defined by Cerberus semantics.

**RATIONALE:**

An example of undefined behavior include division by zero, out of bounds array access, integer overflow and null pointer dereference.

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

In this scenario, after a power-on as each OpenSUT component boots, it attests its state to the Mission Key Management (MKM) component. If the attestation of each component passes, the system will be in a known initial state, fully provisioned. The goal is to ensure that only the application code that has been signed by an external authority (e.g. the trusted component manufacturer) is running on the OpenSUT.

For the purpose of this scenario, we assume that each host computer contains a root of trust, a trusted boot that can bring up the hypervisor. In other words, we assume the host OS to be trusted (see the Threat model). Because hardware root of trust, trusted boot and attestation are all complex topics, only the application code will be attested in this scenario.

We expect the code to be signed with eXtended Merkle Signature Scheme (XMSS), as XMSS is commonly used for firmware signing, and is believed to be quantum safe.

.. _TA2-REQ-20:

Signature of application code image
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-20

Each application code disk image shall contain a digital signature that can be verified by the secure boot.

**Parents:**

- ``[TA2-REQ-19]`` :ref:`TA2-REQ-19`

.. _TA2-REQ-19:

Secure booting only the application code
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-19

Secure boot shall be used to boot only the application code, and only on a subset of OpenSUT components.

**RATIONALE:**

This simplification is consistent with out threat model. Demonstrating Secure Boot only on a subset of components is sufficient.

**Parents:**

- ``[TA2-REQ-18]`` :ref:`TA2-REQ-18`

**Children:**

- ``[TA2-REQ-20]`` :ref:`TA2-REQ-20`

.. _TA2-REQ-18:

Explicit assumptions
~~~~~~~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-18

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

MPS shall Trip on high fuel pressure (sensor to actuation)

.. _TA2-REQ-28:

High temperature trip
^^^^^^^^^^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-28

MPS shall Trip on high temperature (sensor to actuation)

.. _TA2-REQ-29:

Voting logic
^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-29

MPS shall Vote on like trips using two-out-of-four coincidence

.. _TA2-REQ-30:

Automatic actuation
^^^^^^^^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-30

MPS shall Automatically actuate devices.

.. _TA2-REQ-31:

Manual actuation
^^^^^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-31

MPS shall Manually actuate each device upon receiving a user command.

.. _TA2-REQ-32:

Operating modes
^^^^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-32

MPS shall Select mutually exclusive maintenance and normal operating modes on a per division basis.

.. _TA2-REQ-33:

Setpoint adjustment
^^^^^^^^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-33

MPS shall Perform setpoint adjustment in maintenance mode.

.. _TA2-REQ-34:

Maintenance mode bypass
^^^^^^^^^^^^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-34

MPS shall Configure the system in maintenance mode to bypass an instrument channel (prevent it from generating a corresponding active trip output).

.. _TA2-REQ-35:

Maintenance mode forced trip
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-35

MPS shall Configure the system in maintenance mode to force an instrument channel to an active trip output state.

.. _TA2-REQ-36:

Variables displayed
^^^^^^^^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-36

MPS shall Display fuel pressure, and engine temperature.

.. _TA2-REQ-37:

Trip state displayed
^^^^^^^^^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-37

MPS shall Display each trip output signal state.

.. _TA2-REQ-38:

Bypass indication display
^^^^^^^^^^^^^^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-38

MPS shall Display indication of each channel in bypass.

.. _TA2-REQ-39:

Periodic self-test
^^^^^^^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-39

MPS shall run Periodic continual self-test of safety signal path (e.g., overlapping from sensor input to actuation output).

.. _SECTION-OR-MPS-Verification-Requirements:

MPS Verification Requirements
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. _TA2-REQ-21:

Completeness and consistency
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-21

MPS shall demonstrate the Completeness and consistency of requirements

.. _TA2-REQ-22:

Instrumentation independence
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-22

MPS shall demonstrate Independence among the four divisions of instrumentation (inability for the behavior of one division to interfere or adversely affect the performance of another)

.. _TA2-REQ-23:

Instrumentation independence within a division
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-23

MPS shall demonstrate Independence among the two instrumentation channels within a division (inability for the behavior of one channel to interfere or adversely affect the performance of another)

.. _TA2-REQ-24:

Actuation logic independence
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-24

MPS shall demonstrate Independence among the two trains of actuation logic (inability for the behavior of one train to interfere or adversely affect the performance another)

.. _TA2-REQ-25:

Actuation logic independence
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-25

MPS shall demonstrate Completion of actuation whenever coincidence logic is satisfied or manual actuation is initiated

.. _TA2-REQ-26:

Self test and trip independence
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-26

MPS shall demonstrate Independence between periodic self-test functions and trip functions (inability for the behavior of the self-testing to interfere or adversely affect the trip functions)

.. _SECTION-OR-CN-Requirements:

CN Requirements
===============

CN specific requirements, driven by the TA2 needs. In some cases, we mention a more generic *TA1 tooling*, but CN is the main and likely the only tool.

.. _SECTION-OR-Robustness-requirements:

CN Usability requirements
-------------------------

Requirements related to the user experience with CN and TA1 tooling in general.

.. _TA2-REQ-1:

No crashing
~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-1
    * - **STATUS:**
      - Active

CN shall not crash on arbitrary input. Instead, an error message shall be produced.

**RATIONALE:**

Even if a specification is incorrect, or the input file is not a valid C code, CN should gracefully exit.

.. _TA2-REQ-2:

Special delimiters
~~~~~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-2
    * - **STATUS:**
      - Active

CN should support multiple special delimiters, such as `//@` or `/*@` or `/**@`. Which special delimiter should be used can be either configurable, or CN should support all of them at the same time (see TA2-REQ-15).

**RATIONALE:**

In some codebases, CN specs need to co-exist with existing specifications (such as Frama-C ACSL), such that adding CN specs does not break the existing proofs.

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

CN shall run on codebases with multiple specification languages, such as Frama-C, SAW, and Cryptol.

**RATIONALE:**

High assurance code might contain multiple different spec languages, and CN needs to run even in presence of e.g. Frama-C specs.

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

Adding CN specs to a codebase shall not break existing proofs about such codebase.

**RATIONALE:**

For example, adding CN specs into an existing high assurance codebase shall not break the existing Frama-C proofs

**Parents:**

- ``[TA2-REQ-7]`` :ref:`TA2-REQ-7`

.. _TA2-REQ-15:

Project specific CN configuration
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-15

CN shall support project specific configuration, in the form of a configuration file that will adjust how CN behaves.

**RATIONALE:**

This is a top level requirement, further specified in the child requirements.

**Children:**

- ``[TA2-REQ-12]`` :ref:`TA2-REQ-12`
- ``[TA2-REQ-13]`` :ref:`TA2-REQ-13`
- ``[TA2-REQ-14]`` :ref:`TA2-REQ-14`

.. _SECTION-OR-Functional-Requirements:

CN Functional Requirements
--------------------------

This section lists requirements on the functionality of CN, and the features it provides.

.. _TA2-REQ-3:

Versioned releases
~~~~~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-3

CN shall provide versioned releases, such that running CN with `-V` flag shall print out the version of the tool.

.. _TA2-REQ-5:

Variadic functions
~~~~~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-5

CN shall support reasoning about variadic functions, such as `printf()`.

.. _TA2-REQ-4:

Packaged releases
~~~~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-4

CN shall provide packaged releases using industry standard mechanisms, such as docker, or debian packages.

.. _TA2-REQ-6:

C Unions
~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-6

CN shall support reasoning about C union types.

**RATIONALE:**

For example the MPS code relies heavily on unions, and such code needs to be supported.

.. _TA2-REQ-9:

Nested structs
~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-9

CN shall support reasoning about structs composed of other structs.

**RATIONALE:**

For example:
```
struct S {
T1 S1;
T2 *S2;
T3 S3[];
}
```
CN should implicitly enforce that:
1) invariants about struct S1 of type T1 are valid
2) pointer S2 of type T2 is not null, and points to an initialized memory
3) invariants about type T3 are valid for each element of array S3, and this is true for min and max size of S3, with min=0 and max some sensible default value (uint32_MAX?)

.. _TA2-REQ-10:

Specs in header of source file allowed
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-10

CN shall allow the user to write CN specifications in either header (function declaration) or source file (function definition). If CN specs are provided at both function declaration and function definition, CN shall raise an error.

**RATIONALE:**

In some cases, writing specs in the header files is more ergonomic. In other cases, there might be no header files. The user shall have a choice that is the most suitable for a particular codebase. If accidentally the user writes multiple CN specs for the same function (in the header and in the source file), CN needs to throw an error an notify the user, as resolving which specs are valid is a complex problem.

.. _TA2-REQ-12:

Explicit assertion checking
~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-12

CN shall have a configurable option to either ignore inline `assert()` statements, or to statically check them.

**RATIONALE:**

In some codebases, assertions are used only for selective runtime testing, so static checking might produce findings that are not interesting for the developers. The assertions are removed in the production code. Hence having the configurable option for CN is important.

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

If a function is not annotated with any CN specifications, CN shall explicitly state what are the default (implicit) `require`, `ensure` and `modify` clauses.

**RATIONALE:**

It needs to be stated whether by default each function requires and ensures nothing, or if there are some implicit assumptions, important for compositional reasoning. Same for modification - a sensible default behavior could be that a function without specs is assumed to modify everything. However, in that case compositional reasoning is not really possible, so having a configurable option here might be preferred.

The implicit `requires` might encompass e.g. a valid stack frame for the function.

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

CN shall have a configurable option to either assume that all functions are `pure` by default, or to require an explicit `pure` annotation.

**RATIONALE:**

Pure functions are side-effects free, and don't have any persistent static variables (see https://en.wikipedia.org/wiki/Pure_function). In some cases, explicitly stating which functions should be `pure` is easier, while in other codebases, it is reasonable to assume that the functions are `pure` by default. This should be configurable.

**Parents:**

- ``[TA2-REQ-15]`` :ref:`TA2-REQ-15`

.. _SECTION-OR-Documentation-requirements:

CN Documentation requirements
-----------------------------

Documentation of CN, including manuals, tutorials, quick-start guides, code and document generation, and hints and error messages.

.. _TA2-REQ-11:

Generating code documentation with specs
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. list-table::
    :align: left
    :header-rows: 0

    * - **UID:**
      - TA2-REQ-11

TA1 tools shall generate source code documentation that includes CN specification with CN syntax highlighted.

**RATIONALE:**

Doxygen-like documentation with CN specs included is ideal. It is important that the specs are not treated like comments, but are lifted and highlighted in the generated documents.
