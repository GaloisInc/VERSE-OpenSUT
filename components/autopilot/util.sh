# Helpers for `ardupilot_install_deps.sh` and similar scripts.

edo() {
    echo " >> $*" 1>&2
    "$@"
}

# Echo the first argument.  This is useful for expanding a (possible) glob
# pattern to a single concrete filename.
first() {
    echo "$1"
}

# Install a package with `apt-get`, but only if a certain file is missing from
# the system.  Running `apt-get install` on an already-installed package is a
# no-op, but we'd like to avoid asking for `sudo` privileges unnecessarily.
install_if_missing() {
    local package="$1"
    local file="$2"

    # If `$2` is a glob pattern, expand it to the first matching file if one
    # exists.
    if [[ ! -f "$(IFS='' first $file)" ]]; then
        echo "missing $file - need to install package $package" 1>&2
        edo sudo apt-get install -y "$package"
        if [[ ! -f "$(IFS='' first $file)" ]]; then
            echo "actual contents of $package:" 1>&2
            dpkg-query -L "$package" 1>&2
            echo "error: expected package $package to provide $file, but it did not" 1>&2
            return 1
        fi
    fi
}

