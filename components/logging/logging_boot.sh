#!/bin/sh
set -e


# Get environment variables, if needed.  Options for the logging component can
# be set either on the kernel command line or by providing a config file.
if [ -f ./logging_config.sh ]; then
    . ./logging_config.sh
fi


# Parse /proc/cmdline and extract relevant opensut.* options
# https://stackoverflow.com/a/15027935
cmdline_log_device=
cmdline_mkm_host=
cmdline_mkm_port=
cmdline_autopilot_host=
cmdline_autopilot_port=
set -- $(cat /proc/cmdline)
for x in "$@"; do
    case "$x" in
        opensut.log_device=*)
            cmdline_log_device="${x#opensut.log_device=}"
            echo "read log_device='$cmdline_log_device' from /proc/cmdline" 1>&2
            ;;
        opensut.mkm_host=*)
            cmdline_mkm_host="${x#opensut.mkm_host=}"
            echo "read mkm_host='$cmdline_mkm_host' from /proc/cmdline" 1>&2
            ;;
        opensut.mkm_port=*)
            cmdline_mkm_port="${x#opensut.mkm_port=}"
            echo "read mkm_port='$cmdline_mkm_port' from /proc/cmdline" 1>&2
            ;;
        opensut.autopilot_host=*)
            cmdline_autopilot_host="${x#opensut.autopilot_host=}"
            echo "read autopilot_host='$cmdline_autopilot_host' from /proc/cmdline" 1>&2
            ;;
        opensut.autopilot_port=*)
            cmdline_autopilot_port="${x#opensut.autopilot_port=}"
            echo "read autopilot_port='$cmdline_autopilot_port' from /proc/cmdline" 1>&2
            ;;
        # All other options are ignored
    esac
done


# Find the device that contains the logging filesystem.
if [ -n "${VERSE_LOG_DEVICE:-}" ]; then
    log_device="$VERSE_LOG_DEVICE"
    echo "using log device '$log_device' from \$VERSE_LOG_DEVICE" 1>&2
elif [ -n "$cmdline_log_device" ]; then
    log_device="$cmdline_log_device"
    echo "using log device '$log_device' from /proc/cmdline" 1>&2
else
    echo "error: couldn't find a log device from \$VERSE_LOG_DEVICE or /proc/cmdline" 1>&2
    exit 1
fi

# Find MKM host and port
if [ -n "${VERSE_MKM_HOST:-}" ]; then
    mkm_host="$VERSE_MKM_HOST"
    echo "using mkm host '$mkm_host' from \$VERSE_MKM_HOST" 1>&2
elif [ -n "$cmdline_mkm_host" ]; then
    mkm_host="$cmdline_mkm_host"
    echo "using mkm host '$mkm_host' from /proc/cmdline" 1>&2
else
    mkm_host="127.0.0.1"
    echo "using default mkm host '$mkm_host'" 1>&2
fi

if [ -n "${VERSE_MKM_PORT:-}" ]; then
    mkm_port="$VERSE_MKM_PORT"
    echo "using mkm port '$mkm_port' from \$VERSE_MKM_PORT" 1>&2
elif [ -n "$cmdline_mkm_port" ]; then
    mkm_port="$cmdline_mkm_port"
    echo "using mkm port '$mkm_port' from /proc/cmdline" 1>&2
else
    mkm_port="6000"
    echo "using default mkm port '$mkm_port'" 1>&2
fi

# Find autopilot telemetry host and port
if [ -n "${VERSE_AUTOPILOT_HOST:-}" ]; then
    autopilot_host="$VERSE_AUTOPILOT_HOST"
    echo "using autopilot host '$autopilot_host' from \$VERSE_AUTOPILOT_HOST" 1>&2
elif [ -n "$cmdline_autopilot_host" ]; then
    autopilot_host="$cmdline_autopilot_host"
    echo "using autopilot host '$autopilot_host' from /proc/cmdline" 1>&2
else
    autopilot_host="127.0.0.1"
    echo "using default autopilot host '$autopilot_host'" 1>&2
fi

if [ -n "${VERSE_AUTOPILOT_PORT:-}" ]; then
    autopilot_port="$VERSE_AUTOPILOT_PORT"
    echo "using autopilot port '$autopilot_port' from \$VERSE_AUTOPILOT_PORT" 1>&2
elif [ -n "$cmdline_autopilot_port" ]; then
    autopilot_port="$cmdline_autopilot_port"
    echo "using autopilot port '$autopilot_port' from /proc/cmdline" 1>&2
else
    autopilot_port="5762"
    echo "using default autopilot port '$autopilot_port'" 1>&2
fi


# Helper function for fetching the relevant key from the MKM.  Note that if the
# key is needed multiple times (for example, to format the LUKS container and
# then to open it), we request it again each time.  We can't store the key in a
# shell variable because it might contain a null character, and we want to
# avoid writing it to non-encrypted storage.
#
# Requirement TA2-REQ-83: The key for the encrypted filesystem shall be obtained from
# the Mission Key Management component.
#
# For testing, the user can set $VERSE_MKM_CLIENT to override this path.
mkm_client="${VERSE_MKM_CLIENT:-./mkm_client}"
get_key() {
    # Run in a subshell so changes to `$MKM_HOST` don't affect the caller.
    (
        export MKM_HOST="$mkm_host"
        for try in `seq 1 10`; do
            local ret=0
            "$mkm_client" 0 || ret=$?
            if [ "$ret" -eq 0 ]; then
                return 0
            elif [ "$ret" -eq 2 ]; then
                echo "error: key request was rejected by the MKM server" 1>&2
                return 1
            else
                echo "I/O error connecting to MKM server; trying again... ($try/10)" 1>&2
                sleep 2
            fi
        done
        echo "too many I/O errors" 1>&2
        return 1
    )
}


# Check that the log device has a LUKS container

# First, make sure `cryptsetup` works and has LUKS support.  Otherwise we may
# get false negatives when checking with `isLuks`.
cryptsetup_supports_luks() {
    cryptsetup --help | grep isLuks >/dev/null 2>/dev/null
}
if ! cryptsetup_supports_luks; then
    echo "error: cryptsetup doesn't support LUKS encryption" 1>&2
    exit 1
fi

# Requirement TA2-REQ-82: Logs shall be encrypted by storing them on an encrypted
# filesystem.
if ! cryptsetup isLuks "$log_device"; then
    # Requirement TA2-REQ-84: The filesystem shall be initialized on first use.
    echo "formatting uninitialized log device '$log_device'" 1>&2
    get_key | cryptsetup luksFormat --key-file=- "$log_device"
    get_key | cryptsetup luksOpen --key-file=- "$log_device" log_device
    mkfs -t ext2 /dev/mapper/log_device
else
    # Device is already initialized - just open it.
    get_key | cryptsetup luksOpen --key-file=- "$log_device" log_device
fi

mkdir -p /opt/opensut/log
mount /dev/mapper/log_device /opt/opensut/log


# For testing, the user can set $VERSE_LOGGING to override the binary path.
logging="${VERSE_LOGGING:-./logging}"
# TODO: if a real-time clock is unavailable, then the time will be the same on
# each boot (e.g. Jan 1 1970), and newer logs will overwrite older ones.
exec "$logging" "$autopilot_host" "$autopilot_port" \
    >/opt/opensut/log/log-$(date +%Y%m%d-%H%M%S).txt
