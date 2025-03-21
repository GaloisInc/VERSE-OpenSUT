# Trusted boot

- [Trusted boot](#trusted-boot)
  - [Requirements](#requirements)
    - [Functional Requirements](#functional-requirements)
    - [Security Requirements](#security-requirements)
  - [Implementations](#implementations)

## Requirements

### Functional Requirements

* [X] **TA2-REQ-54: Known initial state**
  * The Secure Boot shall bring a given component to a known initial state.
* [X] **TA2-REQ-65: Code attestation**
  * Secure boot shall provide attestation for the application code.
* [X] **TA2-REQ-55: Boot debug information**
  * The Secure Boot shall print information to the console/serial port for debugging purposes.
* **TA2-REQ-56: Secure boot termination**
  * The Secure Boot shall always terminate.
  * **Comment:** CN cannot currently prove termination properties
* [X] **TA2-REQ-57: Launch application or terminate**
  * The Secure boot shall either launch the application, or if an error occurs, log the error and terminate.
* **TA2-REQ-58: Clear memory**
  * The Secure boot shall erase all RAM containing the secure boot data before a handoff to the application code.
  * **Rationale:** This prevents accidental leakage of private information to the potentially compromised application, such as private keys or attestation information.
  * **Comment:** Memory erasing is difficult to achieve for a linux process. This requirement will be relevant for embedded scenarios.


### Security Requirements

* [X] **TA2-REQ-60: Measurement algorithm**
  * The Secure Boot shall use a high assurance implementation of cryptographic algorithms.
  * **Rationale:** For example an implementation that has been formally verified against a "golden" specification, or an implementation automatically generated from such "golden specification".
* [X] **TA2-REQ-59: Binary code measurement**
  * The Secure Boot shall measure the application binary and compare it against a stored good known value.
* **TA2-REQ-61: Secure store of the hash measurement**
  * The Secure Boot should store the measured values in a Trusted Platform Module or other secure memory storage.
  * **Rationale:** Normally this requirement would be binding ("shall"), but given the scope of our threat model, this requirement is optional ("should").
  * **Comment:** A Trusted Platform Module (TPM) is not available.
* [X] **TA2-REQ-62: Abort on mismatched measurements**
  * The Secure Boot shall abort the boot process and throw an error, if the expected and measured values do not match.
* **TA2-REQ-63: Secure Boot stored in read-only memory**
  * The Secure Boot executable shall be stored in a read only memory, or with read-only permissions.
  * **Rationale:** This avoids possible modifications to the secure boot executable.
  * **Comment:** Not implemented, as for simpler execution we run the secure boot and the application code in the same user space.
* [X] **TA2-REQ-64: Do not compare measurements if expected value is not provided**
  * If no expected value of the application binary is provided, the secure boot shall only perform a measurement, save it, and launch the application.
  * **Rationale:** If an application is not signed, the secure boot measurement comparison is disabled.


## Implementations

We provide two trusted boot implementation:

* [firmware.c](./firmware.c) which is based on the original SHAVE trusted boot, and is intended for embedded targets
* [trusted_boot.c](./trusted_boot.c) which is a re-implementation of the functionality provided in `firmware.c` but for linux targets.

Both implementations are verified, but we use `trusted_boot.c` in the OpenSUT, because all components are ran as linux processes. Originally we used SHA256 high assurance implementation for the binary measure, but in our first change event (see [#125](https://github.com/GaloisInc/VERSE-OpenSUT/issues/125)) we added support for XMSS signature verification scheme to the embedded variant of secure boot (`firmware.c`), because the XMSS scheme is suitable for embedded targets.

The `./trusted_boot` binary provides a simplified subset of TPM-like
functionality, including secure boot, measurement, and attestation.  This
implementation is not secure (and isn't designed to be), but it mimics the API
and architecture of a real secure boot implementation.

Running `trusted_boot binary [hash]` will hash `binary` into the "current
measurement", check that the measurement matches `hash` (if provided), and run
`binary` as a child process.  The parent `trusted_boot` process continues
running and provides a simple TPM-like API for its children.  There are two
supported operations:

* `measure`: Takes some binary data as input, hashes it, and mixes the hash
  into the current measurement.
* `attest`: Takes a nonce as input and returns the current measurement and an
  attestation, computed as `HMAC(key, measure || nonce)` using a secret `key`
  embedded in the `trusted_boot` binary.

When `trusted_boot` starts the child, it provides a socket that can be used to
communicate with the `trusted_boot` process and invoke these operations.  The
file descriptor for this socket is provided in the `$VERSE_TRUSTED_BOOT_FD`
environment variable.
