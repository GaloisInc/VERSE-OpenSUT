#!/bin/bash
set -euo pipefail

mkdir -p vms/pkvm-boot

cd linux-pkvm

# Based on the instructions in docs/pKVM/notes019-2020-06-26-pkvm-build.md

make ARCH=arm64 CC=clang CROSS_COMPILE=aarch64-linux-gnu- -j $(nproc) defconfig

# Futz with the configuration to enable the executable spec (and hyp-proxy if
# using the last line):

./scripts/config -d CONFIG_RANDOMIZE_BASE
./scripts/config -e CONFIG_NVHE_EL2_DEBUG
./scripts/config -e CONFIG_PROTECTED_NVHE_STACKTRACE
./scripts/config -d CONFIG_DEBUG_INFO_DWARF_TOOLCHAIN_DEFAULT
./scripts/config -e CONFIG_DEBUG_INFO_DWARF4
./scripts/config --set-val CONFIG_NVHE_EL2_STACKSIZE 5
./scripts/config -e CONFIG_KVM_ARM_HYP_DEBUG_UART
./scripts/config --set-val CONFIG_KVM_ARM_HYP_DEBUG_UART_ADDR 0x09000000
./scripts/config --set-val CONFIG_NVHE_GHOST_MEM_LOG2 22
./scripts/config -e CONFIG_NVHE_GHOST_SPEC
./scripts/config -e CONFIG_PKVM_PROXY # if using the `hyp-proxy` patch

# When building for the first time, the build system will ask you to decide
# between the many configuration options of the executable spec. If you want a
# sensible default that checks everything and prints out failures, use the
# following config settings (BEFORE your call to make):

./scripts/config -k -e CONFIG_NVHE_GHOST_SPEC_CHECK_handle_host_mem_abort
./scripts/config -k -e CONFIG_NVHE_GHOST_SPEC_CHECK___pkvm_host_share_hyp
./scripts/config -k -e CONFIG_NVHE_GHOST_SPEC_CHECK___pkvm_host_unshare_hyp
./scripts/config -k -e CONFIG_NVHE_GHOST_SPEC_CHECK___pkvm_host_reclaim_page
./scripts/config -k -e CONFIG_NVHE_GHOST_SPEC_CHECK___pkvm_host_map_guest
./scripts/config -k -e CONFIG_NVHE_GHOST_SPEC_CHECK___kvm_vcpu_run
./scripts/config -k -e CONFIG_NVHE_GHOST_SPEC_CHECK___pkvm_init_vm
./scripts/config -k -e CONFIG_NVHE_GHOST_SPEC_CHECK___pkvm_init_vcpu
./scripts/config -k -e CONFIG_NVHE_GHOST_SPEC_CHECK___pkvm_teardown_vm
./scripts/config -k -e CONFIG_NVHE_GHOST_SPEC_CHECK___pkvm_vcpu_load
./scripts/config -k -e CONFIG_NVHE_GHOST_SPEC_CHECK___pkvm_vcpu_put
./scripts/config -k -e CONFIG_NVHE_GHOST_SPEC_CHECK___pkvm_guest_share_host
./scripts/config -k -e CONFIG_NVHE_GHOST_SPEC_CHECK___pkvm_guest_unshare_host
./scripts/config -k -e CONFIG_NVHE_GHOST_SPEC_CHECK_handle_guest_mem_abort
./scripts/config -e CONFIG_NVHE_GHOST_SPEC_NOISY
./scripts/config -e CONFIG_NVHE_GHOST_SPEC_COLOURS
./scripts/config -e CONFIG_NVHE_GHOST_DIFF
./scripts/config --set-val CONFIG_NVHE_GHOST_DIFF_MAX_DIFFS_PER_NODE 16
./scripts/config -k -e CONFIG_NVHE_GHOST_DIFF_post_computed
./scripts/config -k -d CONFIG_NVHE_GHOST_DIFF_pre_post_recorded
./scripts/config -k -d CONFIG_NVHE_GHOST_DIFF_post_host_pgtable

./scripts/config -k -d NVHE_GHOST_SPEC_NOISY_handle_host_mem_abort
./scripts/config -k -d NVHE_GHOST_SPEC_NOISY_handle_guest_mem_abort
./scripts/config -e NVHE_GHOST_SPEC_SAFETY_CHECKS
./scripts/config -d NVHE_GHOST_MEM_DUMP_STATS
./scripts/config -d NVHE_GHOST_SPEC_DUMP_STATE
./scripts/config -d NVHE_GHOST_SPEC_VERBOSE
./scripts/config -d NVHE_GHOST_SIMPLIFIED_MODEL

# Now build the kernel image.

make ARCH=arm64 CC=clang CROSS_COMPILE=aarch64-linux-gnu- -j $(nproc) Image
cp -v arch/arm64/boot/Image ../vms/pkvm-boot/vmlinuz-pkvm-verif
