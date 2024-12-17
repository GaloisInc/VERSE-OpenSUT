# MAVLink Telemetry Logging

This is a simple tool for logging telemetry data from Ardupilot.  It connects
to Ardupilot SITL's SERIAL2 port (by default, TCP port 5762), reads MAVLink
messages from that socket, and writes the messages in textual format to stdout.

## Requirements

1. The logging component shall connect to the secondary autopilot telemetry port and record some or all telemetry values to disk.  
   1.1 The logging component shall read MAVlink messages from a socket
2. Logs shall be saved in text format, with a timestamp on each line.  
   2.1. Logs may be printed to stdout for debugging purposes.
3. Logs shall be encrypted by storing them on an encrypted filesystem
4. The key for the encrypted filesystem shall be obtained from the Mission Key Management component
5. The filesystem shall be initialized on first use.

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
