#!/usr/bin/env sh

cd src/components || exit 1

files=( actuator.c )
#instrumentation_common.c
#actuation_unit.c
#instrumentation.c

cn -I ../include -I ../../hardware/SoC/firmware/ --include=../include/wars.h "${files[@]}"
