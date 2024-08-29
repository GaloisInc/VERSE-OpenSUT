#   Copyright 2021, 2022, 2023 Galois, Inc.
#
#   Licensed under the Apache License, Version 2.0 (the "License");
#   you may not use this file except in compliance with the License.
#   You may obtain a copy of the License at
#
#       http://www.apache.org/licenses/LICENSE-2.0
#
#   Unless required by applicable law or agreed to in writing, software
#   distributed under the License is distributed on an "AS IS" BASIS,
#   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#   See the License for the specific language governing permissions and
#   limitations under the License.

ROOT_DIR:=$(shell dirname $(realpath $(firstword $(MAKEFILE_LIST))))


ifeq ($(TARGET),x86_64)
CC = x86_64-linux-gnu-gcc
CXX = x86_64-linux-gnu-g++
GPIO ?= Disabled
LIBGPIOD_BUILD_DIR = build
else ifeq ($(TARGET),aarch64)
CC = aarch64-linux-gnu-gcc
CXX = aarch64-linux-gnu-g++
GPIO ?= Enabled
LIBGPIOD_BUILD_DIR = build.aarch64
else ifeq ($(TARGET),)
# If target is unspecified, use clang and its default target.
CC = clang
CXX = clang++
GPIO ?= Disabled
LIBGPIOD_BUILD_DIR = build
else
$(error "bad TARGET $(TARGET)")
endif

ifeq ($(CONFIG),self_test)
SENSORS = NotSimulated
SELF_TEST = Enabled
else ifeq ($(CONFIG),no_self_test)
SENSORS = NotSimulated
SELF_TEST = Disabled
else ifeq ($(CONFIG),)
# Use default config as defined below
else
$(error "bad CONFIG $(CONFIG)")
endif

CONFIG_SUFFIX = $(foreach x,$(CONFIG),.$(x))
TARGET_SUFFIX = $(foreach x,$(TARGET),.$(x))
BUILD_DIR = build$(CONFIG_SUFFIX)$(TARGET_SUFFIX)

MPS_BIN = mps$(CONFIG_SUFFIX)$(TARGET_SUFFIX)
MPS_BOTTOM_BIN = mps_bottom$(CONFIG_SUFFIX)$(TARGET_SUFFIX)


MODEL_DIR=../models
GEN_DIR=generated
HAND_DIR=handwritten
C_DIR=C
SV_DIR=SystemVerilog

C_GEN_DIR=${GEN_DIR}/${C_DIR}
C_HAND_DIR=${HAND_DIR}/${C_DIR}
SV_GEN_DIR=${GEN_DIR}/${SV_DIR}
SV_HAND_DIR=${HAND_DIR}/${SV_DIR}

ACTUATION_CRY=MPS/ActuationUnit.cry
ACTUATOR_CRY=MPS/Actuator.cry
INSTRUMENTATION_CRY=MPS/InstrumentationUnit.cry

GEN_ACTUATION_UNIT_C = ${C_GEN_DIR}/actuation_unit_impl.c
GEN_ACTUATION_UNIT_SV = ${SV_GEN_DIR}/actuation_unit_impl.sv
GEN_ACTUATION_UNIT_F = Actuate_D0 Actuate_D1 Coincidence_2_4

GEN_ACTUATE_ACTUATOR_C = ${C_GEN_DIR}/actuator_impl.c
GEN_ACTUATE_ACTUATOR_SV = ${SV_GEN_DIR}/actuator_impl.sv
GEN_ACTUATE_ACTUATOR_F = ActuateActuator

GEN_INSTRUMENTATION_C = ${C_GEN_DIR}/instrumentation_impl.c
GEN_INSTRUMENTATION_SV = ${SV_GEN_DIR}/instrumentation_impl.sv
GEN_INSTRUMENTATION_F = Generate_Sensor_Trips Is_Ch_Tripped Trip

GEN_SATURATION_C=${C_GEN_DIR}/saturation_impl.c
GEN_SATURATION_F=Saturation

VERILATED_INC=$(shell verilator --getenv VERILATOR_ROOT)/include
CVERILOG_FLAGS=--yosys-defaults --little-endian

## On the Posix plaform,
## Parallel: pthread-based implementation to simulate the concurrency SoC
## Sequential:  a single-threaded implementation
EXECUTION ?= Parallel

WARNINGS = -Wno-shift-count-overflow -Wpointer-arith -Wcast-align -Werror
WARNINGS += -Wno-shift-op-parentheses # Due to `crymp`
CFLAGS = \
		 -Iinclude \
		 -I$(BUILD_DIR) \
		 -g $(WARNINGS)

CFLAGS += -DPLATFORM_HOST

CC ?= clang
CXX ?= clang++

SENSORS ?= Simulated
# Simulated sensor parameters:
T0 ?= 200 # Initial temperature reading (deg. F)
P0 ?= 1152600 # Initial pressure reading (10^-5 lb/in^2)
T_BIAS ?= 0 # Bias in temp random walk (deg F)
P_BIAS ?= 0 # Bias in pressure random walk
SENSOR_UPDATE_MS ?= 500 # How fast sensors change values

# Indicate in UI if two sensor readings differ by more than the thresholds below:
T_THRESHOLD ?= 3 # (deg. F)
P_THRESHOLD ?= 100 # (10^-5 lb/in^2)

CFLAGS += -DT_THRESHOLD=$(T_THRESHOLD)
CFLAGS += -DP_THRESHOLD=$(P_THRESHOLD)

CFLAGS += -I$(VERILATED_INC) -Wno-deprecated

ifeq ($(SENSORS),Simulated)
CFLAGS += -DSIMULATE_SENSORS -DT_BIAS=$(T_BIAS) -DP_BIAS=$(P_BIAS)
CFLAGS += -DT0=$(T0) -DP0=$(P0)
CFLAGS += -DSENSOR_UPDATE_MS=$(SENSOR_UPDATE_MS)
endif

ifeq ($(EXECUTION),Parallel)
CFLAGS += -DUSE_PTHREADS
LIBS   += -pthread
endif

ifneq ($(SELF_TEST_PERIOD_SEC),)
CFLAGS += -DSELF_TEST_PERIOD_SEC=$(SELF_TEST_PERIOD_SEC)
endif

SELF_TEST ?= Enabled
ifeq ($(SELF_TEST),Enabled)
CFLAGS += -DENABLE_SELF_TEST
endif

DEBUG_PRINT ?= Disabled
ifeq ($(DEBUG_PRINT),Enabled)
CFLAGS += -DDEBUG
endif



OBJS_C = \
  $(BUILD_DIR)/core.c.o \
  $(BUILD_DIR)/common.c.o \
  $(BUILD_DIR)/sense_actuate.c.o \
  $(BUILD_DIR)/variants/actuation_unit_generated_C.c.o \
  $(BUILD_DIR)/variants/actuation_unit_generated_SystemVerilog.cpp.o \
  $(BUILD_DIR)/variants/actuator_generated_C.c.o \
  $(BUILD_DIR)/variants/instrumentation_generated_C.c.o \
  $(BUILD_DIR)/variants/instrumentation_handwritten_C.c.o \
  $(BUILD_DIR)/variants/instrumentation_generated_SystemVerilog.cpp.o \
  $(BUILD_DIR)/variants/instrumentation_handwritten_SystemVerilog.cpp.o \
  $(BUILD_DIR)/variants/saturation_generated_C.c.o \
  $(BUILD_DIR)/components/instrumentation_common.c.o \
  $(BUILD_DIR)/posix_main.c.o
OBJS_VERILATOR = $(BUILD_DIR)/verilator_build/verilated.cpp.o
OBJS_SV = \
  $(BUILD_DIR)/verilator_build/${SV_GEN_DIR}/generate_sensor_trips/VGenerate_Sensor_Trips__ALL.a\
  $(BUILD_DIR)/verilator_build/${SV_GEN_DIR}/is_ch_tripped/VIs_Ch_Tripped__ALL.a\
  $(BUILD_DIR)/verilator_build/${SV_HAND_DIR}/generate_sensor_trips/VGenerate_Sensor_Trips__ALL.a\
  $(BUILD_DIR)/verilator_build/${SV_HAND_DIR}/is_ch_tripped/VIs_Ch_Tripped__ALL.a\
  $(BUILD_DIR)/verilator_build/${SV_GEN_DIR}/actuate_d0/VActuate_D0__ALL.a\
  $(BUILD_DIR)/verilator_build/${SV_GEN_DIR}/actuate_d1/VActuate_D1__ALL.a\
  $(BUILD_DIR)/verilator_build/${SV_GEN_DIR}/actuate_actuator/VActuateActuator__ALL.a

OBJS = $(OBJS_C) $(OBJS_VERILATOR) $(OBJS_SV)


ifeq ($(GPIO),Enabled)
CFLAGS += -DENABLE_GPIO
CFLAGS += -I ../../../src/pkvm_setup/libgpiod/include/
LIBS += \
	-L ../../../src/pkvm_setup/libgpiod/$(LIBGPIOD_BUILD_DIR)/lib/.libs \
	-lgpiod
OBJS_C += $(BUILD_DIR)/gpio_linux.c.o
endif


BUILD_MSG = BUILD CC=$(CC) PLATFORM=$(PLATFORM) EXECUTION=$(EXECUTION) SELF_TEST_PERIOD_SEC=$(SELF_TEST_PERIOD_SEC) SELF_TEST=$(SELF_TEST) GPIO=$(GPIO)

.PHONY: all clean generate_sources generate_c generate_sv

ifneq ($(MPS_BIN),mps)
.PHONY: mps
mps: $(MPS_BIN)
endif

ifneq ($(MPS_BOTTOM_BIN),mps_bottom)
.PHONY: mps_bottom
mps_bottom: $(MPS_BOTTOM_BIN)
endif

all: $(MPS_BIN)

$(MPS_BIN): $(OBJS)
	$(CXX) $(CFLAGS) -o $@ $^ $(LIBS)
	@echo "***"
	@echo $(BUILD_MSG)
	@echo "***"

$(MPS_BOTTOM_BIN): bottom.c
	$(CC) $(CFLAGS) -o $@ bottom.c

self_test_data/tests.inc.c:
	cd self_test_data && \
    CRYPTOLPATH=../${MODEL_DIR} cryptol -b generate_tests.icry && \
    ./test_to_c.py test.csv > tests.inc.c

$(BUILD_DIR)/variants/%_generated_C.c.o: variants/%_generated_C.c generated/C/%_impl.c
	@mkdir -pv $(dir $@)
	$(CC) -c $(CFLAGS) -o $@ $<

# The files listed in $(OBJS_SV) are not used directly, but depending on them
# guarantees that the verilated headers are up to date before this step.
$(BUILD_DIR)/variants/%_SystemVerilog.cpp.o: variants/%_SystemVerilog.cpp $(OBJS_SV)
	@mkdir -pv $(dir $@)
	$(CXX) -c $(CFLAGS) -o $@ $<

$(BUILD_DIR)/%.c.o: %.c self_test_data/tests.inc.c
	@mkdir -pv $(dir $@)
	# `-D_POSIX_C_SOURCE` is required in conjunction with `-std=c11` because
	# otherwise `fileno` and other functions will be omitted from `stdio.h`.
	# `-D_DEFAULT_SOURCE` and `-D_BSD_SOURCE` are required for `usleep`.
	$(CC) -c $(CFLAGS) -o $@ $< -std=c11 \
		-D_POSIX_C_SOURCE=200809L -D_DEFAULT_SOURCE -D_BSD_SOURCE

clean:
	rm -rf build/ build.*/
	rm -f mps mps.*
	rm -f mps_bottom mps_bottom.*

$(BUILD_DIR)/verilator_build/%/generate_sensor_trips/VGenerate_Sensor_Trips__ALL.a: %/instrumentation_impl.sv
	mkdir -p $(dir $@)
	verilator --cc -Wno-WIDTH -Wno-LITENDIAN --top-module Generate_Sensor_Trips $^ \
      -Mdir $(dir $@) --build -MAKEFLAGS CXX=$(CXX)

$(BUILD_DIR)/verilator_build/%/is_ch_tripped/VIs_Ch_Tripped__ALL.a: %/instrumentation_impl.sv
	mkdir -p $(dir $@)
	verilator --cc -Wno-WIDTH -Wno-LITENDIAN --top-module Is_Ch_Tripped $^ \
      -Mdir $(dir $@) --build -MAKEFLAGS CXX=$(CXX)

$(BUILD_DIR)/verilator_build/%/actuate_d0/VActuate_D0__ALL.a: %/actuation_unit_impl.sv
	mkdir -p $(dir $@)
	verilator --cc -Wno-WIDTH -Wno-LITENDIAN --top-module Actuate_D0 $^ \
      -Mdir $(dir $@) --build -MAKEFLAGS CXX=$(CXX)

$(BUILD_DIR)/verilator_build/%/actuate_d1/VActuate_D1__ALL.a: %/actuation_unit_impl.sv
	mkdir -p $(dir $@)
	verilator --cc -Wno-WIDTH -Wno-LITENDIAN --top-module Actuate_D1 $^ \
      -Mdir $(dir $@) --build -MAKEFLAGS CXX=$(CXX)

$(BUILD_DIR)/verilator_build/%/actuate_actuator/VActuateActuator__ALL.a: %/actuator_impl.sv
	mkdir -p $(dir $@)
	verilator --cc -Wno-WIDTH -Wno-LITENDIAN --top-module ActuateActuator $^ \
      -Mdir $(dir $@) --build -MAKEFLAGS CXX=$(CXX)

$(BUILD_DIR)/verilator_build/verilated.cpp.o: $(VERILATED_INC)/verilated.cpp
	@mkdir -pv $(dir $@)
	$(CXX) $(CFLAGS) -c $< -o $@


ifneq ($(REGENERATE_SOURCES),)

generate_sources: generate_c generate_sv

generate_c: ${GEN_ACTUATION_UNIT_C} ${GEN_ACTUATE_ACTUATOR_C} ${GEN_INSTRUMENTATION_C}
generate_sv: ${GEN_ASVTUATION_UNIT_SV} ${GEN_ASVTUATE_ASVTUATOR_SV} ${GEN_INSTRUMENTATION_SV}

${GEN_SATURATION_C}: ${MODEL_DIR}/${INSTRUMENTATION_CRY}
	mkdir -p $(dir $@)
	cd ${MODEL_DIR} && \
		crymp -f ${GEN_SATURATION_F} ${INSTRUMENTATION_CRY} -o ${ROOT_DIR}/${GEN_SATURATION_C}

${GEN_ACTUATION_UNIT_C}: ${MODEL_DIR}/${ACTUATION_CRY}
	mkdir -p $(dir $@)
	cd ${MODEL_DIR} && \
		crymp -f ${GEN_ACTUATION_UNIT_F} ${ACTUATION_CRY} -o ${ROOT_DIR}/${GEN_ACTUATION_UNIT_C}

${GEN_ACTUATION_UNIT_SV}: ${MODEL_DIR}/${ACTUATION_CRY}
	mkdir -p $(dir $@)
	CRYPTOLPATH=${MODEL_DIR} \
    cryptol-verilogc ${MODEL_DIR}/${ACTUATION_CRY} -o ${GEN_ACTUATION_UNIT_SV} \
    ${CVERILOG_FLAGS} \
	$(foreach f,$(GEN_ACTUATION_UNIT_F),--top-level=$(f))

${GEN_ACTUATE_ACTUATOR_C}: ${MODEL_DIR}/${ACTUATOR_CRY}
	mkdir -p $(dir $@)
	cd ${MODEL_DIR} && \
		crymp -f ${GEN_ACTUATE_ACTUATOR_F} ${ACTUATOR_CRY} -o ${ROOT_DIR}/${GEN_ACTUATE_ACTUATOR_C}

${GEN_ACTUATE_ACTUATOR_SV}: ${MODEL_DIR}/${ACTUATOR_CRY}
	mkdir -p $(dir $@)
	CRYPTOLPATH=${MODEL_DIR} \
    cryptol-verilogc ${MODEL_DIR}/${ACTUATOR_CRY} -o ${GEN_ACTUATE_ACTUATOR_SV} \
    ${CVERILOG_FLAGS} \
	$(foreach f,$(GEN_ACTUATE_ACTUATOR_F),--top-level=$(f))

${GEN_INSTRUMENTATION_C}: ${MODEL_DIR}/${INSTRUMENTATION_CRY}
	mkdir -p $(dir $@)
	cd ${MODEL_DIR} && \
		crymp -f ${GEN_INSTRUMENTATION_F} ${INSTRUMENTATION_CRY} -o ${ROOT_DIR}/${GEN_INSTRUMENTATION_C}

${GEN_INSTRUMENTATION_SV}: ${MODEL_DIR}/${INSTRUMENTATION_CRY}
	mkdir -p $(dir $@)
	CRYPTOLPATH=${MODEL_DIR} \
    cryptol-verilogc ${MODEL_DIR}/${INSTRUMENTATION_CRY} -o ${GEN_INSTRUMENTATION_SV} \
    ${CVERILOG_FLAGS} \
	$(foreach f,$(GEN_INSTRUMENTATION_F),--top-level=$(f))

endif
