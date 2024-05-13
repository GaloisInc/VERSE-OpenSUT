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
evaluation will target four independent components, while the final evaluation
will target the fully-assembled system.

| Component                 | Version                                                                                                                                                 | Started as high assurance? | Hypothesis                                                                                                                                                          |
| ------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------- | -------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| iNav                      | [7.1.1](https://github.com/iNavFlight/inav/releases/tag/7.1.1)                                                                                          | No                         | Final version will have fewer vulnerabilities, because applying TA1 tools will mitigate vulnerabilities in the iNav third-party library.                            |
| CZMQ (ZeroMQ)             | [4.2.1](https://github.com/zeromq/czmq/releases/tag/v4.2.1)                                                                                             | No                         | Final version will have fewer vulnerabilities, because applying TA1 tools will mitigate vulnerabilities in the ZeroMQ third-party library.                          |
| SHAVE Trusted Boot        | [baseline-v0.1](https://github.com/GaloisInc/VERSE-OpenSUT/tree/262cd7b435ac97bd00d647a5b53e50a5d61b6f7b/components/platform_crypto/shave_trusted_boot) | Yes                        | Final version will have the same or fewer vulnerabilities; applying TA1 tools will establish similarly high assurance at lower cost than in the original component. |
| Mission Protection System | TBD (est. 2024-05-31)                                                                                                                                   | Yes                        | Final version will have the same or fewer vulnerabilities; applying TA1 tools will establish similarly high assurance at lower cost than in the original component. |

### Scenarios

Because the baseline system is not yet fully assembled, the evaluation will need
to rely on scenarios describing Open SUT intended use to scope the
investigation. Open SUT scenarios are described in
[README.md/Description](../README.md#description).

[README.md/Components](../README.md#components) contains more details about each
component and additional notes on how they will be used.

## Change Events

TBD
