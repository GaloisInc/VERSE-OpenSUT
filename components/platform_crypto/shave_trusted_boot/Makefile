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

TRUSTED_BOOT_BIN = trusted_boot$(TARGET_SUFFIX)

SRC = $(wildcard $(ROOT_DIR)/*.c)
OBJ = $(SRC:$(ROOT_DIR)/%.c=$(BUILD_DIR)/%.o)
CFLAGS = -I$(ROOT_DIR)

CN_FLAGS=-I$(ROOT_DIR) -I$(ROOT_DIR)/../../include --include=$(ROOT_DIR)/../../include/wars.h --magic-comment-char-dollar
CN=cn verify $(CN_FLAGS)

$(TRUSTED_BOOT_BIN): $(OBJ)
	@mkdir -pv $(dir $@)
	$(CC) $(CFLAGS) -o $@ $^

$(BUILD_DIR)/%.o: $(ROOT_DIR)/%.c
	@mkdir -pv $(dir $@)
	$(CC) $(CFLAGS) -c $< -o $@

.PHONY: cn_proof clean
clean:
	rm -rf build/ build.*/
	rm -f $(TRUSTED_BOOT_BIN)

.PHONY: cn_proof_trusted_boot cn_proof_firmware cn_proof_firmware_with_attest
cn_proof: cn_proof_trusted_boot cn_proof_firmware cn_proof_firmware_with_attest

cn_proof_trusted_boot: $(ROOT_DIR)/trusted_boot.c
	$(CN) --skip=parse_hex_str $<
cn_proof_firmware: $(ROOT_DIR)/firmware.c
	$(CN) $<
cn_proof_firmware_with_attest: $(ROOT_DIR)/firmware.c
	$(CN) -DWITH_ATTEST $<
