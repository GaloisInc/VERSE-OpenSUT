#!/bin/bash
set -euo pipefail

if [[ "$(id -u)" -eq "0" ]]; then
    # Drop privileges for the rest of the script.
    cp "$0" /tmp/vm-script
    chown user:user /tmp/vm-script
    exec sudo -u user /bin/bash /tmp/vm-script "$@"
fi

cd ~

sudo apt install -y build-essential

mkdir -p hello
cd hello

# Example code taken from https://wiki.osdev.org/QEMU_AArch64_Virt_Bare_Bones

cat >boot.s <<EOF
.global _start
_start:
    ldr x30, =stack_top
    mov sp, x30
    bl kmain
    b .
EOF

cat >kernel.c <<EOF
#include <stdint.h>

volatile uint8_t *uart = (uint8_t *) 0x09000000;

void putchar(char c) {
    *uart = c;
}

void print(const char *s) {
    while(*s != '\0') {
        putchar(*s);
        s++;
    }
}

void kmain(void) {
     print("Hello world!\n");
}
EOF

cat >linker.ld <<EOF
ENTRY(_start)
SECTIONS {
    . = 0x40100000; /* RAM starts at 0x40000000 but if we ask to load the kernel there, QEMU will not load a DTB */
    .startup . : { boot.o(.text) }
    .text : { *(.text) }
    .data : { *(.data) }
    .bss : { *(.bss COMMON) }
    . = ALIGN(8);
    . += 0x1000; /* 4kB of stack memory */
    stack_top = .;
}
EOF

cat >build.sh <<EOF
#!/bin/bash
set -euo pipefail
as boot.s -o boot.o
gcc -ffreestanding -c kernel.c -o kernel.o
ld -nostdlib -Tlinker.ld boot.o kernel.o -o kernel.elf
EOF
chmod +x build.sh
./build.sh
