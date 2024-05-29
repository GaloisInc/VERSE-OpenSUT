#!/usr/bin/env bash

set -eu
cd components/mission_protection_system || exit 1

files=(
src/components/actuator.c
)

for file in "${files[@]}"
do
cn -I src/include --include=src/include/wars.h  --batch "${file}"
done
