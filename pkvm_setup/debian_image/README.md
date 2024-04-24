# Setup

```sh
# Build the base VM image
bash create_base_vm.sh disk_base.img

# Build the host VM image
bash clone_base_vm.sh disk_base.img disk_host.img
bash run_vm_script.sh disk_host.img setup_host_vm.sh
# Optional: extra setup to make interactive use more convenient
bash run_vm_script.sh disk_host.img setup_host_vm_interactive.sh

# Build the guest VM image
bash clone_base_vm.sh disk_base.img disk_guest.img
bash run_vm_script.sh disk_guest.img setup_guest_vm.sh

# Run the host VM
bash run_vm.sh disk_host.img
# Log in as `user`/`password`, or use `ssh -o Port=8022 user@localhost`.
```

Note: if you resize the terminal while the Debian installer is running, the
display might get corrupted.  Press `^A ^A ^L` to redraw it.  (`^A` is the
escape character for QEMU's terminal multiplexer; `^A ^A` sends `^A` to the VM;
and `^A ^L` causes the `screen` instance that `debian-installer` sets up to
redraw its display.)
