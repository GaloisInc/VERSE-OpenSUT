# Running the OpenSUT under Docker

## Fetch or build the Docker image

To fetch the Docker image:

```sh
# TODO
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
docker build . -t opensut-base
```

## Run the container

```sh
docker run --privileged --rm -it -p 5760:5760 opensut-base:latest
```

Forwarding port 5760 into the container allows MAVProxy on the base machine to
connect to Ardupilot inside the container, which allows the user to start the
mission.  (Specifically, there are several levels of nesting: base machine ->
container -> OpenSUT host VM -> OpenSUT guest VMs.  Ardupilot runs on one of
the OpenSUT guest VMs.)

The `--privileged` flag is necessary to allow opening the encrypted filesystem
where logs are stored after the mission is complete ([see the instructions
below](#read-the-logs)).

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
# FIXME: Switch to base_nested.toml to run the full nested OpenSUT setup
target/release/opensut_vm_runner tests/opensut-dev/base_single.toml
```

Wait for the various OpenSUT VMs to boot.  Usually the logging component is the
last to start up; once it starts printing messages like these, the system is
usually ready:

```
[   35.861091] trusted_boot[276]: connection closed (will retry)
[   37.865934] trusted_boot[276]: connection closed (will retry)
[   39.869003] trusted_boot[276]: connection closed (will retry)
```

TODO: Instructions for installing MAVProxy dependencies (maybe just need to run
`components/autopilot/ardupilot_install_deps.sh`?)

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
3. Switch to tmux window 1 by pressing `^B` `1`.  Press `^B` `x` to close the
   window and stop the OpenSUT VMs, then press `y` to confirm.

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
