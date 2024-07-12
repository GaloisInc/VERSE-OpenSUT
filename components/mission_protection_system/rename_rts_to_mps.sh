#!/bin/bash
set -euo pipefail

readarray -t files < <(
    git ls-files . | while read -r f; do
        if ! [[ -f "$f" ]]; then
            continue
        fi
        if [[ "$(basename "$f")" == "$(basename "$0")" ]]; then
            continue
        fi
        echo "$f"
    done
)

sed -i \
    -e 's/\<HARDENS Reactor Trip System\>/VERSE OpenSUT Mission Protection System/g' \
    -e 's/\<reactor trip system\>/mission protection system/g' \
    -e 's/\(\<\|_\)RTS\(\>\|_\)/\1MPS\2/g' \
    -e 's/\(\<\|_\)rts\(\>\|_\)/\1mps\2/g' \
    "${files[@]}"

for f in "${files[@]}"; do
    g="$(echo "$f" | sed \
        -e 's/\(\<\|_\)RTS\(\>\|_\)/\1MPS\2/g' \
        -e 's/\(\<\|_\)rts\(\>\|_\)/\1mps\2/g' \
    )"
    if [[ "$f" != "$g" ]]; then
        mkdir -p "$(dirname "$g")"
        git mv -v "$f" "$g"
    fi
done
