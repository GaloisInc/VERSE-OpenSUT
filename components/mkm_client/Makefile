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

MKM_CLIENT_BIN = mkm_client$(TARGET_SUFFIX)

SRC = mkm_client.c
OBJ = $(SRC:%.c=$(BUILD_DIR)/%.o)
CFLAGS = -I$(ROOT_DIR) -Wall -Wextra -pedantic

$(MKM_CLIENT_BIN): $(OBJ)
	@mkdir -pv $(dir $@)
	$(CC) $(CFLAGS) -o $@ $^

$(BUILD_DIR)/%.o: $(ROOT_DIR)/%.c
	@mkdir -pv $(dir $@)
	$(CC) $(CFLAGS) -c $< -o $@

.PHONY: clean
clean:
	rm -rf build/ build.*/
