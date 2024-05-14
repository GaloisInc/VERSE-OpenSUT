# Setup

First, install dependencies.  On Debian/Ubuntu:

```sh
# QEMU aarch64 system emulator and tools
sudo apt install qemu-system-arm qemu-utils
# Debian Installer images for aarch64
sudo apt install debian-installer-12-netboot-arm64

# Build dependencies for linux-pkvm / linux-pkvm-verif kernel
sudo apt build-dep linux
```

Now build the host and guest VMs:

```sh
# Build the host and guest disk images.  This takes 1-2 hours.
bash create_disk_images.sh

# Build our patched version of QEMU in the host VM.  This takes 1-2 hours.
bash run_vm_script.sh vms/disk_host.img vm_scripts/install_qemu.sh

# Run the host VM.
bash run_vm.sh vms/disk_host.img
# Log in as `user`/`password`, or use `ssh -o Port=8022 user@localhost`.
```

Note: while the Debian installer is running, resizing the terminal may cause
the installer's display to be corrupted.  If this happens, press `^A ^A ^L` to
redraw it.  (`^A` is the escape character for QEMU's terminal multiplexer; `^A
^A` sends `^A` to the VM; and `^A ^L` in the VM causes the `screen` instance
that `debian-installer` sets up to redraw its display.)


# Running guests

## Linux guest

To run a Linux guest:

* Copy the Linux guest script into the host VM:

  ```sh
  # Outside:
  bash copy_file.sh vms/disk_host.img vm_scripts/run_guest_qemu.sh
  ```

* Start the host VM with the guest disk attached:

  ```sh
  # Outside:
  bash run_vm_nested.sh vms/disk_host.img vms/disk_guest.img
  ```

* Log in to the host VM on the QEMU console or via SSH, as described above.

* Run the Linux guest VM:

  ```sh
  # Host:
  sudo bash run_guest_qemu.sh
  ```

* Log in to the guest VM.

* Shut down the guest VM:

  ```sh
  # Guest:
  sudo poweroff
  ```

* Shut down the host VM:

  ```sh
  # Host:
  sudo poweroff
  ```

## Hello World guest

To run the Hello World guest:

* Build the Hello World kernel image:

  ```sh
  # Outside:
  bash run_vm_script.sh vms/disk_host.img vm_scripts/build_hello_world.sh
  ```

* Copy the Hello World guest script into the host VM:

  ```sh
  # Outside:
  bash copy_file.sh vms/disk_host.img vm_scripts/run_hello_qemu.sh
  ```

* Start the host VM:

  ```sh
  # Outside:
  bash run_vm.sh vms/disk_host.img
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

First, build the pKVM kernel:

```sh
# Outside:
bash build_pkvm.sh
```

Then, boot the host VM and run guests as above, using `run_vm_nested_pkvm.sh`
in place of `run_vm_nested.sh`.

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