# Mission Key Management Client

This is a small helper program for requesting a key from the Mission Key
Management component.  It connects to an MKM server and the local trusted boot
daemon and requests a particular key ID.  The key received is written to
stdout.  If the request fails for any reason, the client program exits nonzero.


## Building

To build the MKM client:

```sh
make
```

Or, to build an ARM binary for use inside the OpenSUT VMs:

```sh
make TARGET=aarch64
```


## Protocol

See `../mission_key_management/README.md` for details on the protocol.

The MKM client connects to localhost (127.0.0.1) port 6000 by default.  To
change this, set the `MKM_HOST` and/or `MKM_PORT` environment variables.
For example, `MKM_HOST=10.0.2.121 MKM_PORT=6001 ./mkm_client` will cause it to
connect to port 6001 on 10.0.2.121.
