# VERSE-OpenSUT

Open System Under Test (OpenSUT) is a fictitious airborne platform that represents a notional high-consequence national security system. OpenSUT is used for evaluation and evolution of VERSE tools.

- [VERSE-OpenSUT](#verse-opensut)
  - [Introduction](#introduction)
    - [How to contribute](#how-to-contribute)
    - [Writing good requirements](#writing-good-requirements)
  - [Description](#description)
    - [Scenario 1: Boot OpenSUT to a known initial state](#scenario-1-boot-opensut-to-a-known-initial-state)
    - [Scenario 2: Load mission key](#scenario-2-load-mission-key)
    - [Scenario 3: Execute a mission](#scenario-3-execute-a-mission)
    - [Scenario 4: Decommission the OpenSUT](#scenario-4-decommission-the-opensut)
  - [Requirements](#requirements)
  - [Models](#models)
    - [Domain Model](#domain-model)
      - [Attestation](#attestation)
      - [Hypervisor](#hypervisor)
    - [Key Distribution](#key-distribution)
      - [Mission Keys](#mission-keys)
      - [pKVM](#pkvm)
      - [Virtual Machine](#virtual-machine)
    - [Threat Model](#threat-model)
    - [SysMLv1 Model](#sysmlv1-model)
    - [AADL Model](#aadl-model)
  - [Code](#code)
  - [Proofs](#proofs)
  - [Components](#components)
    - [Autopilot](#autopilot)
    - [Message Bus](#message-bus)
    - [Mission Key Management (MKM)](#mission-key-management-mkm)
    - [Mission Computer](#mission-computer)
    - [Mission Protection System (MPS)](#mission-protection-system-mps)
    - [Platform Crypto](#platform-crypto)
    - [\[OPTIONAL\] Camera](#optional-camera)
    - [\[OPTIONAL\] External Comms](#optional-external-comms)
    - [\[OPTIONAL\] System Log](#optional-system-log)

## Introduction

This is a companion to the [VERSE Toolchain repository](https://github.com/GaloisInc/VERSE-Toolchain) for TA1.

[ [VERSE project proposal](https://drive.google.com/drive/u/0/folders/1S6wk-aXLZh_dNGU0IcKxB2tnXe5zjV1C) ]

### How to contribute

- Review the [code of conduct](CODE_OF_CONDUCT.md) and [developer guidelines](CONTRIBUTING.md).
- This repository uses [git submodules](https://github.blog/2016-02-01-working-with-submodules/), don't forget to run `git submodule update --init` after cloning the repository.

### Writing good requirements

First, read about how to write good requirements:
* QRA clear requirements [[PDF](./docs/QRA_Clear_Requirements.pdf)]
* [NASA's checklist](https://www.nasa.gov/reference/appendix-c-how-to-write-a-good-requirement/) (shorter)

Then, each requirement consists of:
* a unique identifier
* requirement body
* (optional) a rationale
* (optional) a parent requirement

## Description

> A brief natural-language overview of the purpose, function, operational environment, and degree of complexity of the SUT.


Open System Under Test (OpenSUT) is a fictitious airborne platform that represents a notional high-consequence national security system. OpenSUT contains a [Mission Computer](#mission-computer) which serves as a *flight mission computer*, a [Mission Protection System](#mission-protection-system-mps) which protects the (virtual) engine from getting outside of its safe operating conditions, a [Mission Key Management System](#mission-key-management-mkm) that handles [mission keys](#mission-keys), platform [attestation](#attestation) and provides various cryptographic services. An [autopilot](#autopilot) provides basic flight control and waypoint following ability. The components communicate via point-to-point connections routed through a [messaging bus](#message-bus).

Additional *optional* components might be included, depending on the direction from the client. Those include a [camera](#optional-camera) that provides high-resolution video and a realistic amount of data, a [system logger](#optional-system-log) for logging system events at different classification levels, and [external comms](#optional-external-comms) for communicating with a fictional remote operator for unmanned platform operation.

We are intentionally ambiguous about some details, such as whether the OpenSUT is a manned or unmanned platform (it does have a basic autopilot), or whether it is a fixed wing or a [VTOL](https://en.wikipedia.org/wiki/VTOL). Depending on timing and client needs, we can adapt OpenSUT as necessary.

We intent to build OpenSUT in a way that is similar to industry standards, such as [Open Mission Systems](https://www.vdl.afrl.af.mil/programs/oam/oms.php) (OMS). This means having a publish-subscribe bus, and a well defined set of messages and interfaces.

OpenSUT [components](#components) can be thought of as the *application code*, and each component runs inside a [pKVM](#pkvm) [virtual machine](#virtual-machine). The components run on a set of (simulated) host computers, where at least one is a multi-core CPU running multiple components, and one is a single core CPU hosting a Real-Time-Operating-System (RTOS) and running the [autopilot](#autopilot). Our hypervisor is pKVM capable Linux. All CPUs are ARM64 architecture, because pKVM supports only that instruction set. For easy deployment, we will virtualize the host computers in QEMU instances. Some auxiliary processes, such as a flight simulator, are expected to run directly on the user's machine, or in separate docker containers.

OpenSUT shall operate in the following scenarios:

### Scenario 1: Boot OpenSUT to a known initial state

In this scenario, after a power-on as each OpenSUT component boots, it [attests](#attestation) its state to the [Mission Key Management](#mission-key-management-mkm-module) (MKM) module. If the attestation of each component passes, the system will be in a known initial state, fully provisioned.

### Scenario 2: Load mission key

Once the platform is fully provisioned, load the [mission keys](#mission-keys) to the [Mission Key Management](#mission-key-management-mkm-module) module.
One key is symmetric (e.g., AES256), and one is asymmetric key for a [post-quantum cryptographic](https://en.wikipedia.org/wiki/Post-quantum_cryptography) algorithm (e.g., [KYBER](https://en.wikipedia.org/wiki/Kyber) or Dilithium). The keys are used for the encryption of data both *in transit* (data sent between components) and *at rest* (e.g., stored in [System Log](#system-log)). The platform data have two different classification levels (*low* and *high*), the *low* data are unencrypted, while the *high* data are protected by the mission keys.

### Scenario 3: Execute a mission

After the OpenSUT boots up, initializes to a known state, and loads mission keys, a mission plan is uploaded. The OpenSUT's autopilot then takes off, flies the mission following a set of waypoints, returns to land, and lands at the same position as it started from. 

### Scenario 4: Decommission the OpenSUT

When a mission is completed, or when the OpenSUT is about to be shut down, ensure all data is properly saved to the [System Log](#system-log). The system logs are then exported, and the keys are erased from the [Mission Key Management](#mission-key-management-mkm-module) module. Erase all sensitive data from the OpenSUT.



## Requirements

>Existing requirements (natural-language and/or formal properties) imposed on the SUT, and any
additional requirements identified or formalized during the development process in PROVERS. This
should include top-level “customer” requirements as well as derived or implementation-level
requirements. It should include requirements that TA2 wishes to verify on the SUT, whether or not
this verification has been achieved. Updates in the course of each program phase should reflect new
or changed requirements driving system development.

We will provide top level requirements, as well as refined requirements for each subsystem. Requirements shall be provided as a part of the Magic Draw SysML project, and exported into a plaintext format (likely Markdown) for easier viewing. We will track the requirements throughout the development process - ideally each line of the code will be traceable to one of the top level requirements.


## Models

> Abstractions such as formal or behavioral models/specifications in a systems modeling language, typically used to clarify requirements and to guide verification of an implementation. The models should be accompanied with documentation/metadata making clear how to view, interpret, and/or execute them.

OpenSUT follows the best practices of [Rigorous Digital Engineering](https://galois.com/services/rigorous-digital-engineering/), providing rich models and executable specifications where applicable. The various models will include:

* a [Domain model](#domain-model) defining the most important domain concepts and serving as a glossary of terms
* a [Threat model](#threat-model) for OpenSUT
* a [SysMLv1 model](#sysmlv1-model) delivered as a Cameo/Magic draw project
* an [AADL model](#aadl-model) automatically generated from the SysML model
* combination of generated code and handwritten code annotated CN
* a test suite to validate and deploy the OpenSUT

### Domain Model

Domain model is a part of [Domain Engineering][], and is in its simplest form a [glossary](https://en.wikipedia.org/wiki/Glossary). For our purposes we can think of the domain model as an [ontology](https://en.wikipedia.org/wiki/Ontology_(information_science)). The domain model is expected to grow over time. Following are the most important OpenSUT *domain concepts*:

#### Attestation

* From: https://csrc.nist.gov/glossary/term/attestation

>  The process of providing a digital signature for a set of measurements securely stored in hardware, and then having the requester validate the signature and the set of measurements.

#### Hypervisor

* From: https://csrc.nist.gov/glossary/term/hypervisor

> The virtualization component that manages the guest OSs on a host and controls the flow of instructions between the guest OSs and the physical hardware.

### Key Distribution

* From: https://csrc.nist.gov/glossary/term/key_distribution

> The transport of a key and other keying material from an entity that either owns or generates the key to another entity that is intended to use the key.

#### Mission Keys

Mission keys are a pair of [cryptographic keys](https://csrc.nist.gov/glossary/term/cryptographic_key), issued and valid for a particular mission. First key is used for protecting *high* (or *sensitive*) data *in transit* (i.e. when passed between OpenSUT components), while the second key is used to protect *high* data *at rest* (i.e. in the system log). The keys are typically a combination of one [symmetric key](https://csrc.nist.gov/glossary/term/symmetric_key), and one [asymmetric key](https://csrc.nist.gov/glossary/term/asymmetric_cryptography).


#### pKVM

* also known as **protected-KVM**
* From: https://source.android.com/docs/core/virtualization/security

> pKVM is a KVM-based hypervisor that isolates pVMs and Android into mutually distrusted execution environments. These properties hold in the event of a compromise within any pVM, including the host. Alternative hypervisors that comply with AVF need to provide similar properties.

#### Virtual Machine

* From: https://csrc.nist.gov/glossary/term/virtual_machine

> A simulated environment created by virtualization.

### Threat Model

We are assuming that the underlying hardware, the hypervisor and the virtual machines are *trusted*, while all application code is *untrusted* and thus needs to be verified (unless otherwise noted).

The [hypervisor](#hypervisor) shall ensure space and time separation between components, so even if a single component is compromised, it can affect other components only through already available interfaces (e.g. a point-to-point connection).

We will further clarify our assumptions about component provisioning and [attestation](#attestation), and key distribution.



### SysMLv1 Model

The SysML model is created in Cameo/MagicDraw v2022, and contains:

* [requirements](#requirements)
* top level architecture
* internal block diagrams
* behavioral diagrams (flows and state machines)

Below is a simple top-level SysML block diagram of OpenSUT. **Yellow** blocks contain the application code, and are described in [Components](#components) section. **Red** blocks denote *optional* components. **Green** blocks represent the [hypervisor](#hypervisor) and [pKVM](#pkvm) virtual machine guests. **Blue** blocks represent the underlying ARM64 hardware. The connections between the application components are notional, as any cross-component communication will need to pass through the hypervisor and use virtualized devices.

![OpenSUT-SysML-top-level-view](./docs/figures/OpenSUT-SysML.png)

### AADL Model

We might export the SysML model into AADL with the [CAMET SysML2AADL bridge](https://camet-library.com/camet), in order to facilitate advanced analysis, such as:

* *Schedulability and Schedule generation* with FASTAR tool, to ensure that deadlines for all threads can be met, and a valid schedule (such as ARINC 653) can be generated
* *Multiple Independent Levels of Security* analysis with MILS tooling. It verifies that connected components operate at the same security level and that different security levels are separated with a protective measure like an air gap or an approved cross domain solution. This will be useful for validating that we are appropriately treating the *low* and *high* data

## Code

> Software implementation of the SUT, including clear indication of any external libraries used, build settings, etc. The code should be a snapshot at a minimum, or a full repository with history/branches if feasible.

This repository provides both the model and the implementation of the OpenSUT. Our development practices and the branching structure are summarized in [CONTRIBUTING.md](./CONTRIBUTING.md). CI/CD will be added and expanded as our work progresses.

The main dependency will be a recent version of QEMU that can emulate an ARM64 platform, and a Linux-like OS that can at least run docker. We will use docker as much as possible to package the auxiliary processes, such as a flight simulator. We will provide documentation for installing dependencies and running OpenSUT scenarios.

The repository structure is as follows:

* `components` folder contains code for individual OpenSUT [components](#components) (the *application code*)
* `docs` folder contains related documents, figures, manuals and such
* `models` folder contains SysML and other models of OpenSUT
* `src` folder contains other, *non-application code* such as scripts for spinning up QEMU instances, pKVM virtual machines, test infrastructure etc.

The majority of the code is in C with CN annotations, with some code (such as the [autopilot](#autopilot)) being in C++.


## Proofs

> Artifacts from applying formal methods tools (fully automated or semi-automated) to verify properties of the SUT, including both complete and incomplete verification. This should include the information needed to replicate the verification or to check its mathematical validity.

OpenSUT uses [CN](https://github.com/GaloisInc/VERSE-Toolchain?tab=readme-ov-file#cn) for testing and verification of the application C code. The results of the testing and verification runs (such as logs, counterexamples and other artifacts) are attached to each CI run, and re-generated when OpenSUT is executed locally. Thus a OpenSUT user can easily reproduce out verification results.

We will utilize automated code generation when appropriate, for example use the [SysML model](#sysmlv1-model) for partial test generation, or the [AADL model](#aadl-model) to generate implementation stubs. For most components we have prior specification and models available, written in [Cryptol](https://cryptol.net/), [SAW](https://saw.galois.com/index.html) and/or [Frama-C](https://frama-c.com/). We convert these specifications into CN as a part of our work.

For example, below is a snippet of code from the [Mission Protection System](#mission-protection-system-mps). Function `get_actuation_state()` which reads the actuation signal, has Frama-C specs, that were translated into CN:

```C
// Reading actuation signals
//frama-c
/* @ requires i <= 1;
  @ requires device < NDEV;
  @ requires \valid(value);
  @ assigns *value;
  @ ensures (\result == 0) ==> (*value == 0 || *value == 1);
  @ ensures (\result != 0) ==> (*value == \old(*value));
*/
int get_actuation_state(uint8_t i, uint8_t device, uint8_t *value);
//CN
/*@ spec get_actuation_state(u8 i, u8 device, pointer value)
    requires i <= 1u8;
             device < NDEV();
             take vin = Owned<uint8_t>(value)
    ensures take vout = Owned<uint8_t>(value);
            ((return == 0i32) ? (vout == 0u8 || vout == 1u8) :
             (vout == vin))
@*/
```

Similarly, the function `ActuateActuator()` which controls the engine kill switch, has the following Frama-C and CN specifications:

```C
//frama-c spec function
/*@
  @ // Refines RTS::Actuator::ActuateActuator
  @ logic boolean ActuateActuator(uint8_t input) =
  @   ((input & 0x1) != 0) || ((input & 0x2) != 0);
  @ }
*/

// CN spec function
/*@
function (bool) ActuateActuator(u8 input) {
  ((bw_and_uf(input, 1u8) != 0u8) || (bw_and_uf(input, 2u8) != 0u8))
}
@*/

//frama-c
/* @ assigns \nothing;
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 <==> ((vs & 0x01) || (vs & 0x02));
  @ ensures ActuateActuator(vs) <==> \result == 1;
*/
uint8_t ActuateActuator(uint8_t vs);
//CN
/*@ spec ActuateActuator(u8 vs)
    requires true
    ensures (return == 0u8 || return == 1u8);
      return == 1u8 ? (bw_and_uf(vs, 1u8) != 0u8 || bw_and_uf(vs, 2u8) != 0u8) : true;
      iff(ActuateActuator(vs), return == 1u8)
 @*/
```

In some cases (such as the [Mission Computer](#mission-computer)) no existing specs are available. In those cases we will write CN specifications from scratch, and trace them towards the appropriate [requirements](#requirements).



## Components

**TODO: update components description**

Below we describe each component of the OpenSUT. Component implementation, specs, tests and proofs will be in [components](./components/) folder and/or the architecture model.

### Autopilot

* Source: https://github.com/ArduPilot/ardupilot
* C++
* *Actions*:
  * select a relevant subset of the functionality
  * develop appropriate wrappers for the component
* Description: Flight controller for the platform. Has a certain level of autonomy (waypoint following).

### Message Bus

* Source: [ZeroMQ](https://zeromq.org/) or [Java messaging](https://en.wikipedia.org/wiki/Jakarta_Messaging) implemented as [OpenMQ](https://javaee.github.io/openmq/)
* *Actions*:
  * decide which implementation makes the most sense (they all use TCP under the hood)
  * ZMQ might be a winner since it has a [C implementation](https://zeromq.org/languages/c/)
* Description: P2P connection between endpoints provided by a SW layer. Link layer is handled by a fictitious redundant bus, ensuring packet delivery. Needs to support both *low* and *high* data.

### Mission Key Management (MKM)

* Source: https://gitlab-ext.galois.com/ssith/shave/
  * Alternatives:
    * SpaceBACN (measured boot)
    * SEASHIP (additional crypto)
    * https://github.com/GaloisInc/cryptol-specs
* C / Cryptol / SAW
* *Actions*:
  * select crypto algorithm implementations
  * define / refine application logic
* Description: MKM loads/stores/distributes mission keys, provisions the OpenSUT and provides cryptographic services from [Platform Crypto](#platform-crypto).

### Mission Computer

* *Actions*:
  * define application logic
  * implement this component
* Description: This is the main (mission) computer of the platform. Responsible for flying a mission (similar to *Offboard* mode for PX4 autopilot).

### Mission Protection System (MPS)

* Source: https://github.com/GaloisInc/HARDENS
* C / FramaC
* *Actions*:
  * ACSL specifications need to be translated to CN
  * the language needs to be adjusted to fit an airborne platform (instead of a nuclear reactor)
* Description: an engine protection system. Redundant, measures engine temperature and pressure, and shuts down the engine if unsafe values are detected.

### Platform Crypto

* Source: https://gitlab-ext.galois.com/ssith/shave/
* C / Cryptol / SAW
* *Actions*:
  * select crypto algorithm implementations
  * define / refine application logic
* Description: Tightly integrated with MKM, provides cryptographic services via high-assurance crypto algorithms.

### [OPTIONAL] Camera

* Source: [CASE AADL tutorial](https://github.com/GaloisInc/CASE-AADL-Tutorial/tree/main)
* Description: a generic camera component, should require GPS location from the [Autopilot](#autopilot) to geotag the images. The goal of this component is to stress test the [System Log](#system-log) with a high-data rate video feed.

### [OPTIONAL] External Comms

* Source: Potentially this comes from Sandia National Labs, as they developed a satellite communications board in a PROVERS seedling.  Noah Evans (`nevans@sandia.gov`) is the POC for this line of work.
* Description: C2C/Telemetry stream to a remote operator (e.g. a Ground Control Station).

### [OPTIONAL] System Log

* Source: https://github.com/FreeAndFair/logging/
* Java / JML
* *Actions*:
  * needs to be ported to C (at least a minimal subset)
  * JML specifications need to be translated to CN
* Description: A simple system logger, concurrent & distributed, able to log at different classification levels (*low* and *high*).

[Domain Engineering]: https://en.wikipedia.org/wiki/Domain_engineering
