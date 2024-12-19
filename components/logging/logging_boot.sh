#!/bin/sh
set -e

# Find the device that contains the logging filesystem.
log_device="$VERSE_LOG_DEVICE"

if [ -n "$log_device" ]; then
    echo "found log device '$log_device' from \$VERSE_LOG_DEVICE" 1>&2
fi

if [ -z "$log_device" ]; then
    # Read /proc/cmdline to find opensut.log_device setting
    # https://stackoverflow.com/a/15027935
    set -- $(cat /proc/cmdline)
    for x in "$@"; do
        case "$x" in
            opensut.log_device=*)
                log_device="${x#opensut.log_device=}"
                echo "found log device '$log_device' from /proc/cmdline" 1>&2
                ;;
            # All other options are ignored
        esac
    done
fi

if [ -z "$log_device" ]; then
    echo "error: couldn't find a log device from \$VERSE_LOG_DEVICE or /proc/cmdline" 1>&2
    exit 1
fi


# Helper function for fetching the relevant key from the MKM.  Note that if the
# key is needed multiple times (for example, to format the LUKS container and
# then to open it), we request it again each time.  We can't store the key in a
# shell variable because it might contain a null character, and we want to
# avoid writing it to non-encrypted storage.
mkm_client="${VERSE_MKM_CLIENT:-./mkm_client}"
get_key() {
    # TODO: set $MKM_HOST based on /proc/cmdline
    "$mkm_client" 0
}


# Check that the log device has a LUKS container

# First, make sure `cryptsetup` works and has LUKS support.  Otherwise we may
# get false negatives when checking with `isLuks`.
cryptsetup_suppots_luks() {
    cryptsetup --help | grep isLuks >/dev/null 2>/dev/null
}
if ! cryptsetup_suppots_luks; then
    echo "error: cryptsetup doesn't support LUKS encryption" 1>&2
    exit 1
fi

if ! cryptsetup isLuks "$log_device"; then
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


logging="${VERSE_LOGGING:-./logging}"
# TODO: set telemetry host and port
# TODO: if a real-time clock is unavailable, then the time will be the same on
# each boot (e.g. Jan 1 1970), and newer logs will overwrite older ones.
exec "$logging" >/opt/opensut/log/log-$(date +%Y%m%d-%H%M%S).txt
