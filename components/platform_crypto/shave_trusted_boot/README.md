# Trusted boot

This folder contains a modified Shave trusted boot. It is modified such that it starts an application code as a linux process, and is intended to
run in a guest VM. As of 2d3275e48451ece8c8c146d5681a46d7c547835c the trusted boot performs only a *measurement* of the code (a sha256 sum of the compiled binary), and optionally compares this value with a pre-calculated hash value. The binary is started only if the hash value matches.

## Usage

* build with `make trusted_boot`
* calculate the SHA256 hash of your binary with `sha256sum $MY_BINARY > $MY_BINARY.expected`
* boot with `./trusted_boot $MY_BINARY $MY_BINARY.expected` to include hash comparison, or ``./trusted_boot $MY_BINARY` to only measure and boot, without comparing the expected and actual values
* we are assuming that the value of `$MY_BINARY.expected` cannot be altered

## Measured Boot

The functionality of measured boot is explained [here](https://learn.microsoft.com/en-us/azure/security/fundamentals/measured-boot-host-attestation#measured-boot). To properly chain the hash measurements of individual stages of the boot process, we would need to use a *Trusted Platform Module* (TPM), such as the [QEMU TPM Device](https://qemu-project.gitlab.io/qemu/specs/tpm.html) (see [this page](https://tpm2-software.github.io/2020/10/19/TPM2-Device-Emulation-With-QEMU.html) for an example of a QEMU configuration).

## Attestation

TBD - for proper attestation, we would need a TPM with a pre-shared key, and communication with the Key Management Module.


## NOTES

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
  * load partition or load_elf
  * measure partition
  * compare against stored value
  * (attestation) get nonce from the Attestation service
  * (attestation) send HMAC to the Attestation service
  * launch or exit
* Attestation is about convincing a 3rd party (e.g. Mission Key Management) that the given component can be trusted and is running the expected SW
* If instead of measuring the whole ELF file we wanted to measure only the code/data segments, we could do something like `objcopy -j .text -j .data -j .rodata -O binary rts.self_test rts.self_test.bin` and measure only `rts.self_test.bin`
* Clean up the old Shave artifacts, as we build the assurance case
