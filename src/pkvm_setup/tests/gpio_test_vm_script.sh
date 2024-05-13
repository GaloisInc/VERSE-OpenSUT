#!/bin/bash
set -euo pipefail

# This script runs as root so it can access the GPIO device.

apt install gpiod

gpiod_version="$(gpioget --version | head -n 1)"
case "$gpiod_version" in
    *' v1.'*)
        # v1 command syntax is supported
        ;;
    *)
        # v2 onward use different CLI flags and different output formats
        echo "unsupported gpiod version:"
        echo "$gpiod_version"
        exit 1
esac

DEVICE=gpiochip1

assert_eq() {
    local x=$1
    local y=$2
    local desc=$3
    if [[ "$x" = "$y" ]]; then
        echo "$desc: OK ($x)"
    else
        echo "$desc: FAIL ($x != $y)"
        exit 1
    fi
}

gget() {
    local line=$1
    gpioget "$DEVICE" "$line"
}

gset() {
    local line_and_value=$1
    # Set the line as indicated by `$line_and_value` and hold it in that state
    # for 1 second.  This is hopefully enough time for the external controller
    # to detect the change and update the various input lines.
    gpioset --mode=time --sec=1 "$DEVICE" "$line_and_value"
}

for line in {0..3}; do
    assert_eq "$(gget "$line")" 0 "line $line initial state"
done

# Raising line 0 causes the external controller to toggle the other lines in
# sequence.
for toggle_line in {1..3}; do
    gset 0=1
    for line in {1..3}; do
        expect=0
        if [[ "$line" -eq "$toggle_line" ]]; then
            expect=1
        fi
        assert_eq "$(gget "$line")" "$expect" "line $line after toggle $toggle_line"
    done
done

# Trigger the external controller again to set all lines to 0, then all to 1.
gset 0=1
for line in {1..3}; do
    assert_eq "$(gget "$line")" 0 "line $line all zeros"
done

gset 0=1
for line in {1..3}; do
    assert_eq "$(gget "$line")" 1 "line $line all ones"
done

echo "TEST PASSED"
