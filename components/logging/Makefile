ROOT_DIR:=$(shell dirname $(realpath $(firstword $(MAKEFILE_LIST))))

ifeq ($(TARGET),x86_64)
CC = x86_64-linux-gnu-gcc
CXX = x86_64-linux-gnu-g++
else ifeq ($(TARGET),aarch64)
CC = aarch64-linux-gnu-gcc
CXX = aarch64-linux-gnu-g++
else ifeq ($(TARGET),)
# If target is unspecified, use gcc and its default target.
CC = gcc
CXX = g++
else
$(error "bad TARGET $(TARGET)")
endif

TARGET_SUFFIX = $(foreach x,$(TARGET),.$(x))
BUILD_DIR = build$(TARGET_SUFFIX)

LOGGING_BIN = logging$(TARGET_SUFFIX)

ARDUPILOT_HOME = $(ROOT_DIR)/../autopilot/ardupilot
MAVLINK_XML_DIR = $(ARDUPILOT_HOME)/modules/mavlink/message_definitions/v1.0
MAVLINK_INCLUDE_DIR = $(BUILD_DIR)/gen
MAVLINK_STAMP = $(MAVLINK_INCLUDE_DIR)/mavlink/all/mavlink.h
MAVGEN = $(ARDUPILOT_HOME)/venv/bin/mavgen.py

SRC = logging.c
OBJ = $(SRC:%.c=$(BUILD_DIR)/%.o)
CFLAGS = -I$(ROOT_DIR) -I$(MAVLINK_INCLUDE_DIR) -Wno-address-of-packed-member \
		 -Wall -Wextra -pedantic

$(LOGGING_BIN): $(OBJ)
	@mkdir -pv $(dir $@)
	$(CC) $(CFLAGS) -o $@ $^

$(BUILD_DIR)/%.o: $(ROOT_DIR)/%.c $(MAVLINK_STAMP)
	@mkdir -pv $(dir $@)
	$(CC) $(CFLAGS) -c $< -o $@

# Generate MAVLink protocol headers
$(MAVLINK_STAMP): $(wildcard $(MAVLINK_XML_DIR)/*.xml)
	$(MAVGEN) --lang C --wire-protocol 2.0 --no-validate \
		-o $(MAVLINK_INCLUDE_DIR)/mavlink $(MAVLINK_XML_DIR)/all.xml

.PHONY: clean
clean:
	rm -rf build/ build.*/
