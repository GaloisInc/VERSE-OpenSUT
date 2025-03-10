# Setup

## Glossary

Because we are using multiple nested components, we want to clarify our terminology here.


### Base Platform / Docker Base Image

This is the layer in which the QEMU emulating ARM64 *Host VM* runs. This *can* be your laptop or a workstation,
but for easier dependency management, we are using a *Docker Base Image* which contains all necessary dependencies
and the correct version of QEMU.

This gives us the option to either run multiple Host VMs in a single Base Platform/Image, or we can run each Host VM
in a separate Base Image and connect them with [docker compose](https://docs.docker.com/compose/).


### Host VM

This is the *host* computer emulated in a QEMU. In Phase 1, the host computer is emulated
with an ARM64 architecture, and the *host OS* (hypervisor) is a pKVM capable Linux.
In Phase 2 the host computer will be x86 and the *host OS* (hypervisor) will be Lynx Secure.
The Host VM might be passing some emulated devices to the *guest VM* (such as memory mapped GPIO for the MPS),
on top of a range of virtio devices (such as virtio-net).


### Guest VM

The most nested virtual layer. A virtual machine running a *guest OS* inside the host VM.
Typically the application code (components) would be run on this layer. The guest VM runs as
a KVM guest under QEMU, with the same architecture as the Host VM, so the emulation overhead is minimal.
The *guest OS* can be either a regular Linux, or a unikernel or some other solution capable of handling
virtualized devices (virtio).


## Installation

First, install dependencies.  On the **Base Platform** with [Debian Bookworm](https://www.debian.org/releases/bookworm/) run:

```sh
# QEMU aarch64 system emulator and tools
sudo apt update && apt upgrade
sudo apt install qemu-system-arm qemu-utils
# Debian Installer images for aarch64
# Does not work on Ubuntu:latest
sudo apt install debian-installer-12-netboot-arm64

# Build dependencies for linux-pkvm / linux-pkvm-verif kernel
sudo apt build-dep linux
```

Now build or fetch dependencies and build the VM images:

```sh
bash package.sh full_build vm_runner
bash package.sh full_build vhost_device
# Use `full_build` instead of `download` to build locally
# (this may take several hours)
bash package.sh download pkvm
bash package.sh download qemu
bash package.sh download vm_image_base
bash package.sh full_build vm_images
```


# Running guests

## Linux guest

To run a Linux guest:

* Copy the Linux guest script into the host VM:

  ```sh
  # Base Platform:
  bash copy_file.sh vms/disk_host_dev.img vm_scripts/run_guest_qemu.sh
  ```

* Start the host VM with the guest disk attached:

  ```sh
  # Base Platform:
  bash run_vm_nested.sh vms/disk_host_dev.img vms/disk_guest_dev.img
  ```

* Log in to the host VM on the QEMU console or via SSH, as described above.

* Run the Linux guest VM:

  ```sh
  # Host VM:
  sudo bash run_guest_qemu.sh
  ```

* Log in to the guest VM.

* Shut down the guest VM:

  ```sh
  # Guest VM:
  sudo poweroff
  ```

* Shut down the host VM:

  ```sh
  # Host VM:
  sudo poweroff
  ```

## Hello World guest

To run the Hello World guest:

* Build the Hello World kernel image:

  ```sh
  # Outside:
  bash run_vm_script.sh vms/disk_host_dev.img vm_scripts/build_hello_world.sh
  ```

* Copy the Hello World guest script into the host VM:

  ```sh
  # Outside:
  bash copy_file.sh vms/disk_host_dev.img vm_scripts/run_hello_qemu.sh
  ```

* Start the host VM:

  ```sh
  # Outside:
  bash run_vm.sh vms/disk_host_dev.img
  ```

  The Hello World guest doesn't use the guest disk image, so there's no need to
  pass it through.

* Log in to the host VM on the QEMU console or via SSH, as described above.

* Run the Hello World guest VM:

  ```sh
  # Host:
  bash run_hello_qemu.sh
  ```

  After a second or two, it should print "Hello world!".

* Terminate the guest VM by pressing `^A ^A x`.  (If you are logged into the
  host over SSH, press `^A x` instead.  When logged into the host console, you
  must escape the `^A`, since `^A x` will terminate the host VM instead.)

* Shut down the host VM:

  ```sh
  # Host:
  sudo poweroff
  ```


# Using pKVM

The VM images are built using the pKVM kernel, but don't enable pKVM mode by
default.  To enable it, boot the host VM and run guests as above using
`run_vm_nested_pkvm.sh` in place of `run_vm_nested.sh`.

To check that pKVM is working, check the kernel messages in the host VM:

```sh
# Host:
sudo dmesg | grep kvm
```

With pKVM, the following line should appear:

```
kvm [1]: Protected nVHE mode initialized successfully
```

On a stock Linux kernel using ordinary KVM, the following line will appear
instead:

```
kvm [1]: Hyp mode initialized successfully
```
