# Domain Model

Domain model in its simplest form is a glossary of terms. Following are the most important OpenSUT *domain concepts* (terms):

## Assurance Case

From: https://csrc.nist.gov/glossary/term/assurance_case

> A reasoned, auditable artifact created that supports the contention that its top-level claim (or set of claims), is satisfied, including systematic argumentation and its underlying evidence and explicit assumptions that support the claim(s).

## Attestation

* From: https://csrc.nist.gov/glossary/term/attestation

>  The process of providing a digital signature for a set of measurements securely stored in hardware, and then having the requester validate the signature and the set of measurements.

## Hypervisor

* From: https://csrc.nist.gov/glossary/term/hypervisor

> The virtualization component that manages the guest OSs on a host and controls the flow of instructions between the guest OSs and the physical hardware.

## Key Distribution

* From: https://csrc.nist.gov/glossary/term/key_distribution

> The transport of a key and other keying material from an entity that either owns or generates the key to another entity that is intended to use the key.

## Mission Keys

Mission keys are a pair of [cryptographic keys](https://csrc.nist.gov/glossary/term/cryptographic_key), issued and valid for a particular mission. First key is used for protecting *high* (or *sensitive*) data *in transit* (i.e. when passed between OpenSUT components), while the second key is used to protect *high* data *at rest* (i.e. in the system log). The keys are typically a combination of one [symmetric key](https://csrc.nist.gov/glossary/term/symmetric_key), and one [asymmetric key](https://csrc.nist.gov/glossary/term/asymmetric_cryptography).

## pKVM

* also known as **protected-KVM**
* From: https://source.android.com/docs/core/virtualization/security

> pKVM is a KVM-based hypervisor that isolates pVMs and Android into mutually distrusted execution environments. These properties hold in the event of a compromise within any pVM, including the host. Alternative hypervisors that comply with AVF need to provide similar properties.

## Root of Trust

* From: https://csrc.nist.gov/glossary/term/roots_of_trust

> Highly reliable hardware, firmware, and software components that perform specific, critical security functions. Because roots of trust are inherently trusted, they must be secure by design. Roots of trust provide a firm foundation from which to build security and trust.

## Trusted Boot

* From: https://csrc.nist.gov/glossary/term/trusted_boot

> A system boot where aspects of the hardware and firmware are measured and compared against known good values to verify their integrity and thus their trustworthiness.

## Virtual Machine

* From: https://csrc.nist.gov/glossary/term/virtual_machine

> A simulated environment created by virtualization.
