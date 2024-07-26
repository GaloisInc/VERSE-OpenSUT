# Trusted boot

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

## NOTES

A loose collection of Trusted boot related notes, to be cleaned up in the future.

* Use [EverCrypt APIs](https://hacl-star.github.io/EverCryptDoc.html)
  * [Hashing API](https://hacl-star.github.io/EverCryptHash.html) for SHA-256
    * One-Shot API `EverCrypt_Hash_hash`
    * Otherwise we could use Streaming API and CN could verify that we use it correctly (e.g. `EverCrypt_Hash_Incremental_update` -> `EverCrypt_Hash_Incremental_finish_md5` -> `EverCrypt_Hash_Incremental_free`)
  * [HMAC API](https://hacl-star.github.io/EverCryptHMAC.html), specifically `EverCrypt_HMAC_compute_sha2_256`
  * CN can ensure we call the API correctly
* Normally this works best for embedded devices, where you measure the binary (rather than an elf file).
* Measured boot requires a TPM - might be necessary to provide it in QEMU https://www.qemu.org/docs/master/specs/tpm.html
  * A useful summary is here: https://learn.microsoft.com/en-us/azure/security/fundamentals/measured-boot-host-attestation
* Rough state machine:
  * load partition || load_elf
  * measure partition
  * compare against stored value
  * (attestation) get nonce from the Attestation service
  * (attestation) send HMAC to the Attestation service
  * launch or exit
* Attestation is about convincing a 3rd party (e.g. Mission Key Management) that the given component can be trusted and is running the expected SW

