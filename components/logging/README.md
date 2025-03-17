# MAVLink Telemetry Logging

- [MAVLink Telemetry Logging](#mavlink-telemetry-logging)
  - [Requirements](#requirements)
  - [Building](#building)
  - [Running](#running)
  - [Startup script](#startup-script)


This is a simple tool for logging telemetry data from Ardupilot.  It connects
to Ardupilot SITL's SERIAL2 port (by default, TCP port 5762), reads MAVLink
messages from that socket, and writes the messages in textual format to stdout.

## Requirements

* **TA2-REQ-78: Save telemetry to disk**
  * The logging component shall connect to the secondary autopilot telemetry port and record some or all telemetry values to disk.
* **TA2-REQ-79: Read from a socket**
  * The logging component shall read MAVlink messages from a socket
* **TA2-REQ-80: Log file format**
  * Logs shall be saved in text format, with a timestamp on each line.
* **TA2-REQ-81: Debug print**
  * Logs may be printed to stdout for debugging purposes.
* **TA2-REQ-82: Encrypted storage**
  * Logs shall be encrypted by storing them on an encrypted filesystem
* **TA2-REQ-83: Encryption keys**
  * The key for the encrypted filesystem shall be obtained from the Mission Key Management component
* **TA2-REQ-84: Filesystem initialization**
  * The filesystem shall be initialized on first use.

## Building

The build process involves generating MAVLink protocol headers, which requires
the `mavgen.py` tool and the MAVLink protocol definitions from Ardupilot's
`mavlink` submodule.  Run the `ardupilot_setup_mavgen.sh` helper script to set
up these dependencies:

```sh
bash ../autopilot/ardupilot_setup_mavgen.sh
```

Then build the logging tool:

```sh
make
```

Or, to build an ARM binary for use inside the OpenSUT VMs:

```sh
make TARGET=aarch64
```

## Running

Run `./logging` to connect to the default host and port, which are
`127.0.0.1:5762` (TCP).  It will print each `GLOBAL_POSITION_INT` MAVLink
message that it receives.  Example output:

```
[Mon Nov 11 13:50:48 2024] GLOBAL_POSITION_INT: time_boot_ms=1162589, lat=-353632619, lon=1491652364, alt=584280, relative_alt=-96, vx=1, vy=-2, vz=1, hdg=35256
[Mon Nov 11 13:50:49 2024] GLOBAL_POSITION_INT: time_boot_ms=1163589, lat=-353632619, lon=1491652364, alt=584280, relative_alt=-98, vx=1, vy=-2, vz=1, hdg=35256
[Mon Nov 11 13:50:50 2024] GLOBAL_POSITION_INT: time_boot_ms=1164600, lat=-353632619, lon=1491652364, alt=584270, relative_alt=-107, vx=1, vy=-2, vz=1, hdg=35256
```

Other message types are currently ignored to reduce the total volume of output.

To connect to an alternate host and port, run `./logging <host> <port>`.

To log telemetry data to a file, redirect stdout, as in `./logging >telemetry.log`.

## Startup script

The startup script `logging_boot.sh` mounts an encrypted filesystem (using a
key provided by the Mission Key Management component) and begins logging to a
file on that filesystem.  This is used within the OpenSUT guest VM to start the
logging component.

The script has several options, which can be set through either environment
variables, a config file, or the kernel command line.  In order of precedence:

* In the config file `./logging_config.sh`, set variables using normal shell
  syntax, like `VERSE_FOO="value"`.  This file is sourced at the top of
  `logging_boot.sh`, so variables set here will override the environment
  variables.
* The environment variable `VERSE_FOO` gives the value for option `foo`.
* On the kernel command line (`/proc/cmdline`), an option of the form
  `opensut.foo=value` sets the option `foo` to the string `value`.

The following options are supported:

* `log_device`: This is the path to the device where the encrypted filesystem
  will be set up to store logs.  Within VMs, this is usually a virtual disk
  device like `/dev/vdb`.  When testing the logging component locally, it may
  be more convenient to use a disk image stored in a file, e.g. `logs.img`.
  There is no default for this option; if it's unset, the script will report an
  error.
* `mkm_host`: The IP address for connecting to the MKM server.  The default is
  `127.0.0.1`, which is normally suitable for local testing.  Within the
  OpenSUT, this is usually `10.0.2.123`, which is the IP address assigned to
  the MKM VM (see comments in `create_disk_images.sh`).
* `mkm_port`: The port number for connecting to the MKM server.  The default is
  `6000`, which is the default port used by the MKM.
* `autopilot_host` and `autopilot_port`: The IP address and port number for
  connecting to the autopilot's telemetry port.  The defaults are `127.0.0.1`
  and `5762`; port 5762 is the default telemetry port used by Ardupilot.
  Within the OpenSUT, the IP address is usually `10.0.2.122`.

Some additional environment variables may be useful for testing locally:

* `VERSE_MKM_CLIENT`: Sets the path to the `mkm_client` binary.  The default is
  `./mkm_client`.
* `VERSE_LOGGING`: Sets the path to the `logging` binary.  The default is
  `./logging`.

The script must be run as root so it can initialize (if needed) and mount the
encrypted filesystem.  It also must be run under the `trusted_boot` daemon so
that `mkm_client` can obtain attestations to pass to the MKM server.  Finally,
the MKM must be configured to provide a key to the script; this requires that
the measure be present in the MKM's config file.  When testing locally with
`trusted_boot ./logging_boot.sh`, the correct measure is simply the measure of
`logging_boot.sh` itself (`calc_measure.py --measure-file logging_boot.sh`).
