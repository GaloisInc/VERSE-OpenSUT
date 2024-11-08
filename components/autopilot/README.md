# Submodules

```sh
cd .../verse-opensut

git submodule update --init components/autopilot/ardupilot
bash components/autopilot/ardupilot_init_submodules.sh

git submodule update --init components/autopilot/jsbsim
```

This will initialize only the submodules that are actually needed for our
ArduPilot and JSBSim builds.


# Dependencies

On Debian derivatives, use the install script:

```sh
bash components/autopilot/ardupilot_install_deps.sh
```

On other OSes:

* Install an `aarch64-linux-gnu` toolchain.  The build scripts expect to find
  `aarch64-linux-gnu-gcc` and `aarch64-linux-gnu-g++` in `$PATH`.
* Set up a Python 3 virtualenv (or similar) in the `ardupilot/venv` directory,
  and install the following packages in it:
  `pexpect empy==3.3.4 future pymavlink MAVProxy opencv-python matplotlib wxPython`.  
  If the `wxPython` build fails, you may need to install `libgtk-3` development
  files (on Debian, this is the `libgtk-3-dev` package).


# Building

## ArduPilot

To build the aarch64 binaries for running ArduPilot in the OpenSUT VMs:

```sh
bash src/pkvm_setup/package.sh ardupilot
```

Or, to build a native binary for testing:

```sh
bash components/autopilot/ardupilot_build.sh
```

## ArduPilot application images

```sh
bash src/vm_runner/tests/ardupilot/build_img.sh
```

## JSBSim

```sh
bash components/autopilot/jsbsim_build.sh
```

## `jsbsim_proxy`

```sh
make -C src/jsbsim_proxy
```


# Running

This requires running three different commands in different terminals.

1. JSBSim proxy:

    ```sh
    bash components/autopilot/run_jsbsim.sh
    ```

    This runs the proxy server that will start a JSBSim process once ArduPilot
    connects to it.

2. ArduPilot:

    ```sh
    ( cd src/vm_runner && cargo run -- tests/ardupilot/base_nested.toml )
    ```

    This starts up the OpenSUT VMs and the autopilot component.  Wait until
    ArduPilot is running, as indicated by the output "Waiting for connection
    ....", before continuing.

3. MAVProxy:

    ```sh
    bash components/autopilot/run_mavproxy.sh
    ```

    This starts the MAVProxy ground station software.

Load an example mission by entering the following commands in the MAVProxy
terminal:

```
wp load components/autopilot/ardupilot/Tools/autotest/Generic_Missions/CMAC-circuit.txt
mode auto
```

Wait for the message "pre-arm good" to appear and for the `PRE` indicator to
turn green in the MAVProxy console display, then enter this command in the
MAVProxy terminal to start the mission:

```
arm throttle
```

In the MAVProxy map window, you should see the plane take off and fly to each
of the mission waypoints marked on the map.

To stop the simulation, press ctrl-C in the JSBSim and MAVProxy terminals.
Killing JSBSim will cause the autopilot to exit and the VM to shut down;
however, MAVProxy will keep trying to reconnect to the autopilot and must be
killed separately.
