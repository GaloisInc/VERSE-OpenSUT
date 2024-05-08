Using a recent SAW build (`0.2 (b1a6802)`) the SHA256 verification
herein should run to completion in X minutes.

The HMAC verification currently fails with a error:
{{{
Symbolic execution failed.
All overrides failed: [BadPointerLoad "Invalid memory load: address (29, 0x40:[64]) at type [32 x i8]"]
in hmac_sha256 at internal
}}}
