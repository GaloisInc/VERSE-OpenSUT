# OpenSUT VM Runner

This is a tool for running QEMU VMs or other processes according to a config
file.  The project has two binaries, corresponding to its two modes of
operation:

* `opensut_vm_runner`: Takes a config file as an argument and runs the
  processes described in that config.  This is useful for running on the base
  system to start up the host VM.
* `opensut_boot`: Reads a device path from the kernel command line, mounts that
  device, and runs `opensut_vm_runner` on a config file found there.  This is
  designed to be run in the VM upon boot as a system service or `systemd.run`
  command.  In the future, this can be extended to check for a specific
  signature before mounting the device.

A typical boot process works like this:

* The user runs `opensut_vm_runner` on the base system to start up the host VM.
* The host VM boots and runs `opensut_boot`.
* In the host, `opensut_boot` mounts the host application partition, reads the
  config file, and starts up the guest VM.
* The guest VM boots and runs `opensut_boot`.
* In the guest, `opensut_boot` mounts the guest application partition, reads
  the config file, and starts up some application process such as MPS.


## Setup

First, run the setup steps in `../pkvm_setup/` to build the base disk images
for the host and guest VMs.

There are two options for building the `vm_runner` binaries:

1.  Cross-compile for aarch64 from the local machine:

    ```sh
    cargo build --release --target aarch64-unknown-linux-gnu
    ```

    This may require installing additional Rust target libraries.

2.  Compile inside a VM:

    ```sh
    cargo run -- build_config.toml
    ```

    This will start up the development version of the host VM, install a Rust
    toolchain (if needed), and compile `vm_runner`.  This will usually be
    slower than the cross-compiling option.

Finally, install the new `vm_runner` binaries into the host and guest VMs:

```sh
cargo run -- install_config.toml
cargo run -- install_config_guest.toml
```


## Usage

The `tests/` directory contains some example configurations.

To run a trivial Hello World script:

```sh
cargo run -- tests/hello_guest.toml
```

This should print "Hello, World!"

The remaining tests require building Hello World application images first:

```sh
bash tests/build_hello_image.sh
```

To run the Hello World script inside a VM:

```sh
cargo run -- tests/hello_base_single.toml
```

This will start up a VM with an application image containing `hello_guest.toml`
and `hello.sh`.  This will produce a large amount of output as Linux boots
within the VM, consisting of kernel messages, a group of "starting service"
messages, and a group of "stopped service" messages.  Between the start group
and the stop group, output like the following should appear:

```
         Starting kernel-command-li…ommand from Kernel Command Line...
[   19.241859] squashfs: version 4.0 (2009/01/31) Phillip Lougher
[   19.326691] opensut_boot[303]: Hello, World!
[  OK  ] Finished kernel-command-li… Command from Kernel Command Line.
```

To run the Hello World script inside two nested VMs:

```sh
cargo run -- tests/hello_base_nested.toml
```

This is similar to the previous example, but there will be two sets of Linux
startup and shutdown messages, one for the host and one for the guest.  In the
middle should be output like this:

```
[   68.312436] opensut_boot[301]:          Starting kernel-command-li…ommand from Kernel Command Line...
[   68.498854] opensut_boot[301]: [   45.040450] squashfs: version 4.0 (2009/01/31) Phillip Lougher
[   68.757693] opensut_boot[301]: [   42.171542] opensut_boot[307]: Hello, World!
[   68.814990] opensut_boot[301]: [  OK  ] Finished kernel-command-li… Command from Kernel Command Line.
```


## Expected hash

`opensut_boot` can be configured to check that the SHA256 hash of the
application image matches an expected value before mounting the image.  The
expected hash value is read as a hex string from
`$OPENSUT_EXPECTED_APP_IMAGE_HASH`.  If the SHA256 hash of the image doesn't
match this value, `opensut_boot` panics without mounting the image.

The easiest way to use this feature in a VM's boot process is to set
`OPENSUT_EXPECTED_APP_IMAGE_HASH=xxx` on the VM's kernel command line.  Because
the key `OPENSUT_EXPECTED_APP_IMAGE_HASH` doesn't contain a dot, it's
interpreted as an environment variable for the `init` process.  The
`opensut-boot.service` and `opensut-trusted-boot.service` systemd units are
then configured to pass that variable through to the `opensut_boot` process.
