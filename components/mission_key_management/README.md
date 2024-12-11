# Mission Key Management Server

This server processes key requests and distributes keys to other components.
Any component can connect to the MKM, request a key, and attest to the code
that it's running; the MKM will then send the key if allowed by the MKM's
built-in policy.


## Building

To build the MKM server:

```sh
make
```

Or, to build an ARM binary for use inside the OpenSUT VMs:

```sh
make TARGET=aarch64
```


## Protocol

The protocol that components use to communicate with the MKM works as follows:

1. The client connects to the MKM over TCP.
2. The client component sends a key ID (1 byte), indicating which key it is
   requesting.
3. The MKM sends a random nonce (16 bytes).
4. The client obtains an attestation matching the challenge (by communicating
   with its trusted boot daemon) and sends the attestation (64 bytes).
5. If the attestation is valid and MKM policy allows the component to receive
   the requested key, the MKM sends the key (32 bytes).

If an error occurs, such as an invalid attestation or a policy violation, the
MKM simply closes the connection without sending the key.

Since all messages have a fixed size and occur in a fixed order, the protocol
does not use any headers or delimiters for messages.

The MKM server listens on localhost (127.0.0.1) port 6000 by default.  To
change this, set the `MKM_BIND_ADDR` and/or `MKM_PORT` environment variables.
For example, `MKM_BIND_ADDR=0.0.0.0 MKM_PORT=6001 ./mkm` will cause it to
listen on port 6001 on all network interfaces.
