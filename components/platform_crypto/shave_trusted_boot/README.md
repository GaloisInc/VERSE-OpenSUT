# Trusted boot

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
