# Running ArduPilot SITL with external JSBSim

```sh
verse_opensut=/path/to/verse-opensut

# Terminal #1: Start jsbsim_proxy
cd $verse_opensut/components/autopilot/ardupilot/Tools/autotest/
# Must have `JSBSim` in $PATH
command -v JSBSim || echo "JSBSim not found"
$verse_opensut/src/jsbsim_proxy/jsbsim_proxy JSBSim \
    --suspend \
    --simulation-rate=1200 \
    --logdirectivefile=jsbsim_fgout_0.xml \
    --script=jsbsim_start_0.xml \
    --nice=0.00000001

# Terminal #2: Start arduplane
cd $verse_opensut/components/autopilot/ardupilot/Tools/autotest/
build/sitl/bin/arduplane \
    --synthetic-clock \
    --model jsbsim_ext \
    --speedup 1 \
    --slave 0 \
    --defaults Tools/autotest/default_params/plane-jsbsim.parm

# Terminal #3: Start mavproxy
cd $verse_opensut/components/autopilot/ardupilot/Tools/autotest/
. venv/bin/activate
mavproxy.py \
    --master tcp:127.0.0.1:5760 \
    --map \
    --console
```

In the `mavproxy` terminal, enter the following commands to load an example
mission:

```
wp load Tools/autotest/Generic_Missions/CMAC-circuit.txt
mode auto
```
Wait for the `PRE` (pre-arm) indicator in the `mavproxy` console window to turn
green, then enter this in the `mavproxy` terminal:

```
arm throttle
```

In the `mavproxy` map window, the plane should take off and fly in a loop
around the mission waypoints.
