# Mission Key Management Server

- [Mission Key Management Server](#mission-key-management-server)
  - [Building](#building)
  - [Configuration](#configuration)
  - [Protocol](#protocol)
  - [Requirements](#requirements)

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

## Configuration

The MKM server takes a config file describing which keys it should distribute
to which other components.  The config is initially written as an INI file (a
text-based format), then converted to a binary format that's easier for the
`mkm` binary to parse.

To produce a binary config file for testing:

```sh
python3 convert_config.py test_config.ini test_config.bin
```

This will read `test_config.ini`, which is the config file used for MKM's
automated tests, and will output `test_config.bin`.


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
For example, `MKM_BIND_ADDR=0.0.0.0 MKM_PORT=6001 ./mkm config.bin` will cause
it to listen on port 6001 on all network interfaces.

## Requirements

* [X] **TA2-REQ-66: Close connection on error**
  * If an error occurs at any time during the key exchange protocol, such as an invalid attestation or a policy violation, the MKM shall close the connection without sending the key.
* [X] **TA2-REQ-67: No headers or delimiters for messages**
  * All MKM messages shall have a fixed size and occur in a fixed order, and the protocol shall not use any headers or delimiters for messages.
* [X] **TA2-REQ-68: TCP connection**
  * The client shall connect to the MKM over TCP via a socket.
* [X] **TA2-REQ-69: Wait for key ID**
  * While the MKM is ready to receive connections, a client component shall send a key ID (1 byte), indicating which key it is requesting.
* [X] **TA2-REQ-70: Send challenge**
  * When a key ID is received from a client, the MKM shall send a random nonce (16 bytes) in return.
* [X] **TA2-REQ-71: Valid key ID**
  * The MKM shall process only a valid key ID.
* [X] **TA2-REQ-72: Calculate attestation**
  * Once the client receives an attestation challenge (nonce) from the MKM, the client shall compute the response by communicating with its trusted boot daemon and send the response back to the MKM.
* [X] **TA2-REQ-73: Challenge response format**
  * The challenge response shall be computed by concatenating the current measured value (matching the expected hash of the binary) with the received nonce, and then computing HMAC of the concatenated value using a secret key. The resulting response is 64 bytes long.
* [X] **TA2-REQ-74: Secure boot secret key**
  * The secret key may be identical across different components, so as to simplify the key management. This key is known at build time to the MKM.
  * **Rationale:** In real world, secure boot would store unique and shared keys in a Hardware Root of Trust (HROT) and the decision whether to use unique or shared keys would be based on the actual threat model. In either way, the MKM must know the key to validate the attestation response.
* [X] **TA2-REQ-75: Receive response**
  * Once the MKM receives the attestation response, it shall check its validity. A valid attestation is calculated as described in TA2-REQ-73.
* [X] **TA2-REQ-76: Send key**
  * If the received response is valid, the MKM shall send back to the client the associated mission key and terminate the connection.
* [x] **TA2-REQ-77: Key format**
  * The mission key is 32-bytes long symmetric AES key.
