# Setup

```sh
# Build the host and guest disk images.  This takes 1-2 hours.
bash create_disk_images.sh

# Run the host VM.
bash run_vm.sh vms/disk_host.img
# Log in as `user`/`password`, or use `ssh -o Port=8022 user@localhost`.
```

Note: while the Debian installer is running, resizing the terminal may cause
the installer's display to be corrupted.  If this happens, press `^A ^A ^L` to
redraw it.  (`^A` is the escape character for QEMU's terminal multiplexer; `^A
^A` sends `^A` to the VM; and `^A ^L` in the VM causes the `screen` instance
that `debian-installer` sets up to redraw its display.)
