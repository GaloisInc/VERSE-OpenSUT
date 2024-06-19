# Trusted boot

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
  * load partition || load_elf
  * measure partition
  * compare against stored value
  * (attestation) get nonce from the Attestation service
  * (attestation) send HMAC to the Attestation service
  * launch or exit
* Attestation is about convincing a 3rd party (e.g. Mission Key Management) that the given component can be trusted and is running the expected SW
