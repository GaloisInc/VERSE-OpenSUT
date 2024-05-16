# Experimental Setup

The VERSE Open SUT serves as a case study for evaluating formal methods tools as
applied to high-assurance system development. The Open SUT is built from a
collection of preexisting components of varying levels of assurance. Some are
lightly modified to target a flight controller scenario, while others are left
unchanged, representing the challenges of working with third-party libraries.

We anticipate two kinds of experiments:

1. Red team analysis
1. Change events

The VERSE hypothesis is that a strong assurance toolchain will increase the
assurance of low-assurance components, mitigate risk in third-party components,
and maintain the high level of assurance in high-assurance components with lower
time, effort, and expertise.

## Red Team Analysis

Red Balloon Security will perform a preliminary evaluation of a baseline version
of the Open SUT and then a second evaluation of the final system. The baseline
evaluation will target five independent components (two of them high assurance), while the final evaluation
will target the fully-assembled system. We describe the assumptions and limitations for the each component below.

As stated in the [threat model](../README.md#threat-model), we are assuming that the underlying emulated hardware, and the host OS are *trusted*, while the hypervisor and the virtual machines and all application code is generally *untrusted*.


### SHAVE Trusted Boot

* Started as high assurance? **Yes**
* Version: [baseline-v0.1](https://github.com/GaloisInc/VERSE-OpenSUT/tree/262cd7b435ac97bd00d647a5b53e50a5d61b6f7b/components/platform_crypto/shave_trusted_boot)
* Hypothesis:
  * *Final version will have the same or fewer vulnerabilities; applying TA1 tools will establish similarly high assurance at lower cost than in the original component.*
* Scoping:
  * We intend to use the SHAVE Trusted Boot for attesting the application code before launching it. Likely we will be using a variation of SHAVE Trusted Boot to start most of the components.

### Mission Protection System (MPS)

* Started as high assurance? **Yes**
* Version: [HARDENS @ 54ac1d8](../components/mission_protection_system/HARDENS/)
* Hypothesis:
  * *Final version will have the same or fewer vulnerabilities; applying TA1 tools will establish similarly high assurance at lower cost than in the original component.*
* Scoping:
  * The baseline version of MPS is the original HARDENS code. MPS will be our first ported component, and adapting the HARDENS code for MPS will be our first change event. The expected delivery of a verified MPS is on 2024-05-31

### pKVM

* Started as high assurance? **No**
* Version: `pkvm-core-6.4`
* Hypothesis:
  * *Final version will have fewer vulnerabilities, **if** we apply TA1 tools will to mitigate vulnerabilities in the pKVM, beyond what has already been verified.*
* Scoping:
  * The partially verified branch is `pkvm-verif-6.4` (see [this paper](https://dl.acm.org/doi/pdf/10.1145/3571194) for details)
  * We might be verifying more of the pKVM code, but it is not the primary focus of Phase 1 (as mentioned in the [README](../README.md) we are primarily focusing on the application code)

### Message Bus

* Started as high assurance? **No**
* Version:
  * [4.2.1](../components/message_bus/czmq/)
* Hypothesis:
  * *Final version will have fewer vulnerabilities, because applying TA1 tools will mitigate vulnerabilities in the ZeroMQ third-party library.*
* Scoping:
  * The message bus is connecting almost all components, and we will attempt to ensure correct use of the ZMQ API, but adding verification to the ZMQ codebase is lower priority than the other components.

### Ardupilot

* Started as high assurance? **No**
* Version: [4.5](../components/autopilot/ardupilot/)
* Scoping:
  * Based on the OpenSUT [scenarios](../README.md#description), the autopilot is providing only adjacent functionality to the OpenSUT. The primary use case of the OpenSUT is correctly booting the system, and then loading keys and managing sensitive information. Flying a mission with the autopilot is the 3rd scenario in the list.
  * Because of that, and because the code is in C++ we are **not** planning to verify the autopilot with TA1 tools. If some critical bugs that would be relevant to the OpenSUT scenarios are found, we will address them, but otherwise we do not expect to change the Ardupilot code in Phase 1




### Scenarios

Because the baseline system is not yet fully assembled, the evaluation will need
to rely on scenarios describing Open SUT intended use to scope the
investigation. Open SUT scenarios are described in
[README.md/Description](../README.md#description).

[README.md/Components](../README.md#components) contains more details about each
component and additional notes on how they will be used.

## Change Events

The first change event is to modify the HARDENS protection system such that it fits the engine protection domain and runs inside the OpenSUT environment. We will track our change events as we proceed with the development of OpenSUT.
