# EMB3D Threat Model

This document analyses the [threats](https://emb3d.mitre.org/threats/) enumerated by the [EMB3D Threat Model](https://emb3d.mitre.org/). Rather than mapping the properties to threats in the [properties mapper](https://emb3d.mitre.org/properties-mapper/), we decided to explicitly address the threats, such that we can provide more context why we think certain threats are in or out of scope.

## Hardware

OpenSUT runs on QEMU emulated ARM64 hardware, and making hardware configurations (beyond the minimum needed for booting and running the OpenSUT), modifications or protections is out of scope for TA2. OpenSUT has some UART ports to components, and those can be used for access. We do not assume unrestricted physical access to the hardware, and we consider the hardware related threats *TID-101 ... TID-119* to be out of scope.

Note that one scenario we discussed is when OpenSUT is recovered by the adversary during a mission, and thus the adversary has an unlimited physical access. That is a valid concern, and while we can provide recommendations how we *would* protect against a physical access, implementing such protections is out of scope for us, given our timeline and budget.

## System Software

Most of the system software threats are considered out of scope, as the hypervisor is assumed to be trusted, and the Guest VM OS (currently Linux) is simply a convenient way to spin up the application software (this is given by the limitations of pKVM, which makes running non-linux guests complicated). In Phase 2 we expect to be switching to Lynx OS, should mitigate the OS related threats.

* *Root of trust* related properties (*PID-251* and *PID-252*) are interesting, and the related threats (*TID-214* and *TID-220*) are very relevant for real systems, however properly implementing a Root Of Trust on OpenSUT is out of scope for us, given our timeline and budget. If needed, we can provide recommendations how one would implement a RoT, given our previous experience with such.
* *PID-242 Device includes hypervisor* property, and [TID-208](https://emb3d.mitre.org/threats/TID-208) and [TID-209](https://emb3d.mitre.org/threats/TID-209) threats are relevant, as compromised application code can affect the virtual machine. Verifying the VM code is out of scope (although prior work on formal verification of pKVM has been done by the Cambridge team), thus we need to mitigate these threads by verifying the application code.
* The following properties apply to OpenSUT application code:
  * *PID-272 Device includes cryptographic firmware/software integrity protection mechanisms*
  * *PID-2721 Device includes a shared key for firmware integrity validation*
  * *PID-2722 Device includes digitally signed firmware (with private key)*
  * We mitigate the associated threats by using formally verified cryptographic libraries, and by formally verifying the secure boot code. Secure boot is used to launch the application code only - this is an intentionally contrived scenario, demonstrating the importance of upgrade integrity verification, while fitting our timeline and budget.
* Other system software properties do not apply to OpenSUT.

## Application Software

The majority of threats is connected to the application code, which is untrusted. As a result, we are focusing our efforts to harden the application code with the TA1 tools.

* *PID-31 Application-level software is present and running on the device* and [TID-301](https://emb3d.mitre.org/threats/TID-301) is in scope, and needs to be addressed by the TA1 tools.
* *PID-3122 Device includes support for manual memory management programming languages (e.g. C, C++)* property applies to OpenSUT, as the majority of the code is in C, and some in C++. [TID-327](https://emb3d.mitre.org/threats/TID-327) is the first threat that needs to be addressed by the TA1 tools.
* *PID-331 Device includes unauthenticated services* applies in some cases, e.g. the maintenance UART port for Mission Protection System. We might address this issue by adding user authentication to the maintenance port.
* *PID-332 Device includes authenticated services* applies in some cases, the related threats should be mitigated by using formally verified cryptographic libraries, and formally verified application code (with TA1 tools).
* *PID-3322 Device includes cryptographic mechanism to authenticate users and sessions* applies, and the related threats should be mitigated by using formally verified cryptographic libraries, and formally verified application code (with TA1 tools).

## Networking

Because we are using ZMQ which in turn relies on the OS's network stack, some of the networking threats are relevant. Because the OS itself is considered *trusted* (both on the Guest VM and the Host VM), we are not hardening the OS network stack. We are also not attempting to mitigate any of the threats related to services, e.g. *TID-401 ... TID-407*.

Some notable threats:
* [TID-406](https://emb3d.mitre.org/threats/TID-406) - would be ideally mitigated by a proper hypervisor (such as Lynx Secure) which will open channels only between specific components, based on a config file autogenerated from the system architecture model. However, in Phase 1 it is possible that a compromised application code opens a connection to any other part of the system (since the underlying communication relies on ZMQ). Thus verification of all component communication code has high priority. Note we are *not* planning to verify any part of ZMQ, but only the application code interfacing with the ZMQ API.
* [TID-408](https://emb3d.mitre.org/threats/TID-408) - we prevent this threat by encrypting the sensitive data with the mission keys anytime the data is in transit.
* Threats related to *PID-4113 Device includes cryptographic functions for sensitive data, such as encryption or authentication* - we mitigate these by using formally verified cryptographic libraries, and strong cryptographic algorithms, as well as formally verifying any application code that uses cryptographic APIs.
* [TID-412](https://emb3d.mitre.org/threats/TID-412) - is out of scope for us, as we rely on the OS services and ZMQ to route messages
