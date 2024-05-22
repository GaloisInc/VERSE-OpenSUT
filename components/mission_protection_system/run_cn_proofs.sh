#!/usr/bin/env bash

cd src/components || exit 1

files=( actuator.c
instrumentation_common.c
actuation_unit.c
instrumentation.c
)

cn -I ../include --include=../include/wars.h "${files[@]}"
