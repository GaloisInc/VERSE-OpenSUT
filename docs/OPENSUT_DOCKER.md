# Running the OpenSUT under Docker

Running the OpenSUT under Dcoker consists of the following steps:

1. start the base docker image
3. run `vm_runner` with the `opensut-dev/base_nested.toml` config
4. `vm_runner` spins up one VM (the QEMU-emulated *host* computer)
5. this *host* acts as a *hypervisor* and spins up 4 separate VMs
6. each of these 4 VM runs one component
7. each component is booted via the secure boot
8. the secure boot checks the measurement of the binary against the expected (pre-computed) measure and boots only if those two value match
9. the logging component performs an attestation in order to get data-at-rest encryption key from the Mission-Key-Management component
10. all components are operational, and a mission can be executed (the flight simulator is running as a separate non-virtualized process on the base image, and the MavProxy is running natively outside of the docker container on the user's laptop)
11. after the mission, all computers are gracefully shut down

The scripts below automate a number of these steps.


## Install dependencies

Most dependencies are preinstalled within the OpenSUT Docker image.  However,
the graphical MAVProxy tool, which is required to start the autopilot mission,
must be run on the host machine.  To install MAVProxy and other Ardupilot
dependencies:

```sh
bash components/autopilot/ardupilot_install_deps.sh
```

## Fetch or build the Docker image

To fetch the Docker image:

```sh
docker pull ghcr.io/galoisinc/verse-opensut/opensut-base:latest
```

Building the Docker image from scratch first requires building all of the
OpenSUT components.

```sh
# Install system dependencies
sudo apt-get install -y \
    build-essential autoconf automake autoconf-archive cmake \
    gcc-aarch64-linux-gnu g++-aarch64-linux-gnu \
    verilator \
    python3-pip \
    qemu-system-arm qemu-utils

# Dockerfile expects `packages/` directory to have no extraneous files.
rm -f packages/*

# Build packages

# Use `download foo -u USERNAME` instead of `full_build foo` if you have an
# Artifactory API key
bash src/pkvm_setup/package.sh full_build pkvm
bash src/pkvm_setup/package.sh full_build qemu
bash src/pkvm_setup/package.sh full_build vm_image_base

bash src/pkvm_setup/package.sh full_build trusted_boot
bash src/pkvm_setup/package.sh full_build libgpiod
bash src/pkvm_setup/package.sh full_build vm_runner
bash src/pkvm_setup/package.sh full_build ardupilot
bash src/pkvm_setup/package.sh full_build logging
bash src/pkvm_setup/package.sh full_build vhost_device
bash src/pkvm_setup/package.sh full_build mkm
bash src/pkvm_setup/package.sh full_build mkm_client
bash src/pkvm_setup/package.sh full_build vm_images

# Build Docker image
docker build . -t ghcr.io/galoisinc/verse-opensut/opensut-base:latest
```

## Run the container

```sh
docker run --privileged --rm -it -p 5760:5760 ghcr.io/galoisinc/verse-opensut/opensut-base:latest
```

Forwarding port 5760 into the container allows MAVProxy on the base machine to
connect to Ardupilot inside the container, which allows the user to start the
mission.  (Specifically, there are several levels of nesting: base machine ->
container -> OpenSUT host VM -> OpenSUT guest VMs.  Ardupilot runs on one of
the OpenSUT guest VMs.)

The `--privileged` flag is necessary to allow opening the encrypted filesystem
that contains telemetry logs after the mission is complete ([see the
instructions below](#read-the-logs)).

## Run the mission

Within the container, run `tmux`.

In the first tmux window, start `jsbsim_proxy`:

```sh
bash components/autopilot/run_jsbsim.sh
```

Press `^B` `c` to create a second tmux window.  In the second window, start the
OpenSUT:

```sh
cd src/vm_runner
target/release/opensut_vm_runner tests/opensut-dev/base_nested.toml
```


Wait for the various OpenSUT VMs to boot.  The logging component is typically
the last to start up; once it starts printing messages like these, the system
is usually ready:

```
[  192.441966] opensut_boot[367]: [  164.897292] trusted_boot[273]: connect error (will retry): Connection refused
[  194.517320] opensut_boot[367]: [  166.911533] trusted_boot[273]: connect error (will retry): Connection refused
[  196.506175] opensut_boot[367]: [  168.911342] trusted_boot[273]: connect error (will retry): Connection refused
```

The other components write their output to separate files to avoid causing
confusion by interleaving messages.  If you need to inspect their output, open
a new tmux window by pressing `^B` `c`, examine the files
`src/vm_runner/serial.*.txt` (`tail -F` may be useful for following the boot
process of a specific component), and finally close the tmux window by pressing
`^D` at the shell.

Now, in a separate terminal on the base system, run MAVProxy:

```sh
bash components/autopilot/run_mavproxy.sh
```

MAVProxy should start up and connect to the autopilot component.  As described
in the [autopilot README](../components/autopilot/README.md), load the example
mission, wait for the `PRE` (pre-arm) indicator to turn green, and start the
mission:

```
wp load components/autopilot/ardupilot/Tools/autotest/Generic_Missions/CMAC-circuit.txt
mode auto
# Wait until `PRE` is green
arm throttle
```

In the MAVProxy map window, you should see the plane take off and fly toward
the waypoints.

The plane will continue flying until manually stopped.  To stop it:
1. Press `^C` in the terminal where you started MAVProxy.  This should close
   both MAVProxy windows.
2. In the container, switch to tmux window 0 by pressing `^B` `0`, then press
   `^C` to stop JSBSim.
3. Switch to tmux window 1 by pressing `^B` `1`.  Wait for the logging
   component to shut down, as indicated by the following messages:
   ```
   [  365.446443] opensut_boot[367]: [  342.192954] systemd-shutdown[1]: All filesystems, swaps, loop devices, MD devices and DM devices detached.
   [  365.576932] opensut_boot[367]: [  342.349081] systemd-shutdown[1]: Syncing filesystems and block devices.
   [  365.649712] opensut_boot[367]: [  342.441684] systemd-shutdown[1]: Powering off.
   ...
   [  365.964894] opensut_boot[367]: [  342.758193] reboot: Power down
   ```
   Press `^B` `x` to close the window and stop the remaining OpenSUT VMs, then
   press `y` to confirm.

## Read the logs

First, get the encryption key from the MKM config file:

```sh
cd src/vm_runner
key=$(grep key0 tests/opensut-dev/mkm_config.ini | cut -d\  -f3)
```

Next, open and mount the encrypted filesystem:

```sh
echo "$key" | xxd -r -p | cryptsetup luksOpen --key-file=- logging_data.img logging_data
mount /dev/mapper/logging_data /mnt
```

Finally, read the logs:

```sh
ls /mnt
less /mnt/log-*.txt
```

There should be several entries recorded during startup all with roughly the
same latitude, longitude, and altitude, followed by entries where these fields
vary as the autopilot flies the mission.

Afterward, close the encrypted filesystem (otherwise it will remain open on the
host after the container has terminated):

```sh
umount /mnt
cryptsetup luksClose logging_data
```
