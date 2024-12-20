ROOT_DIR:=$(shell dirname $(realpath $(firstword $(MAKEFILE_LIST))))

$(opam env)
CN=cn verify --magic-comment-char-dollar --include=$(ROOT_DIR)/../include/wars.h -I $(ROOT_DIR)/../include -I $(OPAM_SWITCH_PREFIX)/lib/cerberus/runtime/libc/include/posix

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

MKM_BIN = mkm$(TARGET_SUFFIX)

SRC = mkm.c client.c policy.c sha_256.c hmac_sha256.c
OBJ = $(SRC:%.c=$(BUILD_DIR)/%.o)
CFLAGS = -I$(ROOT_DIR) -Wall -Wextra -pedantic

$(MKM_BIN): $(OBJ)
	@mkdir -pv $(dir $@)
	$(CC) $(CFLAGS) -o $@ $^

$(BUILD_DIR)/%.o: $(ROOT_DIR)/%.c
	@mkdir -pv $(dir $@)
	$(CC) $(CFLAGS) -c $< -o $@

.PHONY: clean
clean:
	rm -rf build/ build.*/

.PHONY: cn_proof
cn_proof:
	$(CN) client.c