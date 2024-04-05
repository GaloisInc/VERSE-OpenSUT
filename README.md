# VERSE-OpenSUT

Open System Under Test (OpenSUT) is an airborne platform that represents a notional high-consequence national security system.
OpenSUT is a fictitious airborne platform and is used for evaluation and evolution of VERSE tools.

- [VERSE-OpenSUT](#verse-opensut)
  - [Domain Model](#domain-model)
  - [Requirements](#requirements)
  - [Scenarios](#scenarios)
    - [Scenario 1: Boot entire OpenSUT to a known initial state](#scenario-1-boot-entire-opensut-to-a-known-initial-state)
    - [Scenario 2: Load mission key](#scenario-2-load-mission-key)
    - [Scenario 3: Execute a mission](#scenario-3-execute-a-mission)
    - [Scenario 4: Decommission the OpenSUT](#scenario-4-decommission-the-opensut)
  - [Components](#components)
    - [Autopilot](#autopilot)
    - [Message bus](#message-bus)
    - [Mission Key Management (MKM)](#mission-key-management-mkm)
    - [Mission Processing](#mission-processing)
    - [Mission Protection System (MPS)](#mission-protection-system-mps)
    - [Platform Crypto](#platform-crypto)
    - [\[OPTIONAL\] Camera](#optional-camera)
    - [\[OPTIONAL\] External Comms](#optional-external-comms)
    - [\[OPTIONAL\] System Log](#optional-system-log)


## Domain Model

Domain model is in its simplest form a [glossary](https://en.wikipedia.org/wiki/Glossary), but for our purposes think of the domain model as an [ontology](https://en.wikipedia.org/wiki/Ontology_(information_science)).

TBD

## Requirements

First, read about how to write good requirements:
* QRA clear requirements [[PDF](./docs/QRA_Clear_Requirements.pdf)]
* [NASA's checklist](https://www.nasa.gov/reference/appendix-c-how-to-write-a-good-requirement/) (shorter)

Then, each requirement consists of:
* a unique identifier
* requirement body
* (optional) a rationale
* (optional) a parent requirement

## Scenarios

First, we describe scenarios relevant for the OpenSUT.

### Scenario 1: Boot entire OpenSUT to a known initial state

Each component boots, and attests its state to the [Mission Key Management](#mission-key-management-mkm-module) module.

### Scenario 2: Load mission key

Once the platform is fully provisioned, load two mission keys to the [Mission Key Management](#mission-key-management-mkm-module) module.
One key is symmetric (e.g. AES256), and one is asymetric key for a [post-quantum cryptographic](https://en.wikipedia.org/wiki/Post-quantum_cryptography) algorithm (e.g. [KYBER](https://en.wikipedia.org/wiki/Kyber) or Dillithium). The keys are used for the encryption of data both *in transion* (data sent between components) and *at rest* (e.g. stored in [System Log](#system-log)). The platform data have two different classification levels (*low* and *high*), the *low* data are unencrypted, while the *high* data are protected by the mission keys.

### Scenario 3: Execute a mission

After the OpenSUT boots up, initializes to a known state, and loads mission keys, it takes off, flies an actual mission (e.g. follow a couple of waypoints), and lands.

### Scenario 4: Decommission the OpenSUT

When a mission is completed, or when the OpenSUT is about to be shut down, ensure all data is properly saved to [System Log](#system-log), logs are exported, and the keys are erased from the [Mission Key Management](#mission-key-management-mkm-module) module. Erase all sensitive data from the OpenSUT.


## Components

Second, we describe each component of the OpenSUT. Note that eventually we move the description of each component to [components](./components/) folder and/or the architecture model.

### Autopilot

* Source: https://github.com/ArduPilot/ardupilot
* C++
* *Actions*:
  * select a relevant subset of the functionality
  * develop appropriate wrappers for the component
* Description: Flight controller for the platform. Has a certain level of autonomy (waypoint following).


### Message bus

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
* Description: MKM loads/stores/distributes mission keys, provisions the OpenSUT and provides cryptographic services from [Platform Crypto](#platform-crypto)

### Mission Processing

* *Actions*:
  * define application logic
  * implement this component
* Description: This is the main (mission) computer of the platform. Responsible for flying a mission (similar to *Offboard* mode for PX4 autopilot).

### Mission Protection System (MPS)

* Source: https://github.com/GaloisInc/HARDENS
* C / FramaC
* *Actions*:
  * FramaC needs to be ported to CN
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

* Description: C2C/Telemetry stream to a remote operator (e.g. a Ground Control Station)

### [OPTIONAL] System Log

* Source: https://github.com/FreeAndFair/logging/
* Java / JML
* *Actions*:
  * needs to be ported to C (at least a minimal subset)
* Description: A simple system logger, concurrent & distributed, able to log at different classification levels (*low* and *high*)
