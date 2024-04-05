# How to get, build, and run pKVM
# 2020-06-26 .. 2024-02-27


Kayvan Memarian, Ben Simner, Peter Sewell.  Originally based on notes from Will Deacon and Andrew Scull.


These instructions assume things get checked out in `$REPOS`.

# Get tooling
## Get clang
### Easy way

From your package manager (anything more recent than version 11 should work):
```
sudo apt install clang # on debian based distribution
```

```
brew install clang # on linux or macos if using homebrew

```
Versions that are known to work:
  * on linux: `clang-r475365b` (from Android's prebuilts repo below. Probably also later versions, but we haven't tested)
  * on linux: `clang-15` (ubuntu `clang-15` package, version `1:15.0.7-0ubuntu0.22.04.3`)
  * on macos: `clang-17` (version 17.0.6 installed using homebrew)

### Harder way

Get the the prebuilt toolchain from AOSP:
```
cd $REPOS
git clone https://android.googlesource.com/platform/prebuilts/clang/host/linux-x86
```
(warning: this is _huge_. There's probably a smart way to avoid cloning the whole thing.)

## Get Arm GNU Toolchain (AArch64)

From your package manager:
```
sudo apt install gcc-aarch64-linux-gnu # on debian based distribution
```

Or download binary from ARM's website:
[https://developer.arm.com/downloads/-/arm-gnu-toolchain-downloads](https://developer.arm.com/downloads/-/arm-gnu-toolchain-downloads)

This is only needed for the assembler, etc., not gcc proper

## Get QEMU

From your package manager:
```
sudo apt install qemu-system-arm # on debian based distribution
```

```
brew install qemu # on linux or macos if using homebrew
```

Versions of qemu that are known to work:
  * on ubuntu: version 6.2.0 (installed with apt: package `qemu-system-arm`, version `1:6.2+dfsg-2ubuntu6.16`)
  * on macos: version 8.2.1 (installed with homebrew)

NOTE: on Apple silicon avoid version 8.2.0 and some 8.1.X as they have an issue with the EFI firmware.


# Get linux kernel with pKVM

The Android source repo is `https://android-kvm.googlesource.com/linux`.

Our working fork is `https://github.com/rems-project/linux`, with the main branches:

- `pkvm-core-6.4` - the base upstream version that we're currently working above, from the eponymous branch of `https://android-kvm.googlesource.com/linux`
- `pkvm-verif-base-6.4` - this is `pkvm-core-6.4` plus Cambridge hacks for printing from EL2 and increasing EL2 stack size
- `pkvm-verif-6.4` - the working version for executable spec (based on top of `pkvm-verif-base-6.4`)
- `hyp-proxy` - this is `pkvm-core-6.4` plus a patch by Thibaut Pérami, which enables EL0 to do hypercalls for testing purposes
- `pkvm-verif-6.4+hyp-proxy` - this is the executable spec (`pkvm-verif-6.4`) plus Thibaut's `hyp-proxy` patch (CAUTION: this is meant as an example; we do not keep it in sync with `pkvm-verif-6.4`)
- `pkvm-verif-cn-bv` - the working version for CN proof

Get the desired version with e.g.:
```
cd $REPOS
git clone https://github.com/rems-project/linux.git  # 12 min
cd linux
git fetch origin pkvm-verif-6.4+hyp-proxy
git switch pkvm-verif-6.4+hyp-proxy
```

# Build linux kernel with pKVM

NOTE: these instructions will only work on linux (NOT on macos).

```
cd $REPOS/linux
```

To clean (from the top-level linux Makefile comments):
```
# Cleaning is done on three levels.
# make clean     Delete most generated files
#                Leave enough to build external modules
# make mrproper  Delete the current configuration, and all generated files
# make distclean Remove editor backup files, patch leftover files and the like
```

## Install the build dependencies
You need a few things installed to build the kernel. On a debian-based distribution, do:

```
sudo apt install make bison flex bc libssl-dev
```


## Configure
```
make ARCH=arm64 CC=clang CROSS_COMPILE=aarch64-linux-gnu- -j $(nproc) defconfig
```
(If your clang is not in PATH, you need to adapt `CC` accordingly)

Futz with the configuration to enable the executable spec (and `hyp-proxy` if using the last line):
```
./scripts/config -d CONFIG_RANDOMIZE_BASE
./scripts/config -e CONFIG_NVHE_EL2_DEBUG
./scripts/config -d CONFIG_DEBUG_INFO_DWARF_TOOLCHAIN_DEFAULT
./scripts/config -e CONFIG_DEBUG_INFO_DWARF4
./scripts/config --set-val CONFIG_NVHE_EL2_STACKSIZE 5
./scripts/config -e CONFIG_KVM_ARM_HYP_DEBUG_UART
./scripts/config --set-val CONFIG_KVM_ARM_HYP_DEBUG_UART_ADDR 0x09000000
./scripts/config --set-val CONFIG_NVHE_GHOST_MEM_LOG2 22
./scripts/config -e CONFIG_NVHE_GHOST_SPEC
./scripts/config -e CONFIG_PKVM_PROXY # if using the `hyp-proxy` patch
```

When building for the first time, the build system will ask you to decide between the many configuration options of the executable spec.
If you want a sensible default that checks everything and prints out failures, use the following config settings (BEFORE your call to `make`):
```
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
```

## Build
```
make ARCH=arm64 CC=clang CROSS_COMPILE=aarch64-linux-gnu- -j $(nproc) Image
```

(Again, if your clang is not in the PATH, you need to adapt CC accordingly)

This builds `$REPOS/linux/arch/arm64/boot/Image`, with `.nvhe.o` object files in the pKVM source directories which are what get linked into the eventual EL2 part of the image.


# Running tests in our bare-bones Linux boot environment

The repo [https://github.com/rems-project/pkvm-tester](https://github.com/rems-project/pkvm-tester) provides a minimal setup to run our (in progress) test suite on kernels that have hyp-proxy enabled. This runs everything in an initramfs image, without the need for a full user space installation (e.g. debian). This requires `zsh`, `make` and `jq` and the previously installed `qemu-system-aarch64`.
```
sudo apt install zsh make jq
```

```
cd $REPOS
git clone https://github.com/rems-project/pkvm-tester.git
cd pkvm-tester/
./scripts/fetch-sample-prebuilt
```

The last line downloads a prebuilt executable of the testsuite into the `payload/` directory. This was built from the github repo [`rems-project/pkvm-proxy-ocaml`](https://github.com/rems-project/pkvm-proxy-ocaml/).

To run the tests, do:
```
./scripts/run-vm --kernel $REPOS/linux/arch/arm64/boot/Image
```

The prebuilt testsuite (as of 29 feb 2024) runs the following tests:
* kernel share
  - host shares 1 page with pKVM.

* kernel share+unshare
  - host shares and then unshares 1 page with pKVM.

* vm init+deinit
  - host initialises a VM with 1 vCPU, initialises the vCPU, and then tears
    down the VM. This involves the sharing/unsharing of several pages from
    host to pKVM.

* vcpu load+put
  - same as the previous, but the vCPU is loaded and then unloaded ("put")
    before tearing down the VM.

* vcpu run
  - same as the previous, but this time code is loaded in the VM using
    `__pkvm_host_map_guest()` and the vCPU is run. The loaded code performs
    one memory load, which causes a data abort bringing control back to the host.

* guest hvc version
  - host creates a VM with 1 vCPU as the previous test, but the loaded page of code
    contains a single (guest) hypercall which just returns the SMCC version number.

* guest hvc mem_share
  - same as previous, but instead the guest hypercall shares 1 page between the guest and host.

* guest hvc mem_unshare
  - same as previous, but before the guest returns, does a second hypercall to unshare that page with the host.

# Booting a full linux distribution in QEMU

## Grab some EFI firmware

You need a prebuilt UEFI firmware for QEMU to use. Depending on your operating system you can find it here:

* on debian base distribution (includes Ubuntu), install `qemu-efi-aarch64`:
    ``` 
    sudo apt-get install qemu-efi-aarch64
    ``` 
    This installs the firmware at `/usr/share/qemu-efi-aarch64/QEMU_EFI.fd`

* on linux and macos, if you have installed QEMU using homebrew (`brew install qemu`)
the firmware is at: `$(brew --prefix qemu)/share/qemu/edk2-aarch64-code.fd`

* as a last resort, you can manually download the file from the debian package repository from [https://packages.debian.org/sid/all/qemu-efi-aarch64/download](https://packages.debian.org/sid/all/qemu-efi-aarch64/download), e.g. in some temporary directory do:

    ```
    wget http://ftp.uk.debian.org/debian/pool/main/e/edk2/qemu-efi-aarch64_2024.02-1_all.deb
    ar -x qemu-efi-aarch64_2024.02-1_all.deb
    tar xf data.tar.xz
    ```

    This produces the file `./usr/share/qemu-efi-aarch64/QEMU_EFI.fd`

## Install the host

Installing the host requires us to boot our newly acquired firmware and start the Debian installer from there. We'll create the host environment in a new directory

```
cd $REPOS
mkdir qemu-host
cd qemu-host/
```
With that, let's go!

### Create a disk

Before we can dive into the installer, we'll need a disk on which to install the new distribution. The `qemu-img` utility makes this dead easy:
```
cd $REPOS/qemu-host
qemu-img create -f qcow2 disk.img 16G
```
Notice how the `qcow2` format allows the file to expand as necessary, so don't be afraid to make the thing bigger if you want to.

### Prepare the firmware

We need a couple of flash partitions to hold the UEFI firmware we downloaded earlier along with its variables to track things such as the boot partition etc.:
```
cd $REPOS/qemu-host
truncate -s 64m varstore.img
truncate -s 64m efi.img
dd if=/usr/share/qemu-efi-aarch64/QEMU_EFI.fd of=efi.img conv=notrunc
```
IMPORTANT: You must enter these commands exactly as shown, otherwise you will almost certainly run into problems later on.

### Grab some install media

We'll need some install media to boot into initially. I just grabbed the latest stable Debian net installer:
```
cd $REPOS/qemu-host
wget https://cdimage.debian.org/debian-cd/current/arm64/iso-cd/debian-12.5.0-arm64-netinst.iso

```

### Boot the sucker  (with a vanilla debian)

It can be a bit daunting driving QEMU, so I usually wrap this one up in a script:
```
cd $REPOS/qemu-host
qemu-system-aarch64 -M virt \
  -machine virtualization=true -machine virt,gic-version=3    \
  -cpu cortex-a72 -smp 2 -m 4096                              \
  -drive if=pflash,format=raw,file=efi.img,readonly=on        \
  -drive if=pflash,format=raw,file=varstore.img               \
  -drive if=virtio,format=qcow2,file=disk.img                 \
  -device virtio-scsi-pci,id=scsi0                            \
  -object rng-random,filename=/dev/urandom,id=rng0            \
  -device virtio-rng-pci,rng=rng0                             \
  -device virtio-net-pci,netdev=net0                          \
  -netdev user,id=net0,hostfwd=tcp::8022-:22                  \
  -nographic                                                  \
  -drive if=none,id=cd,file=debian-12.5.0-arm64-netinst.iso   \
  -device scsi-cd,drive=cd
```
(Andrew Scull remarked: I'd also recommend changing `-cpu max,sve=off` to `-cpu cortex-a72`.
This means QEMU will emulate a cpu that doesn't support VHE so you won't
accidently find yourself in the wrong mode.)


That brings up an installer within the terminal, with standard interactive questions.  Enter the defaults for everything except "United Kingdom" (or whatever, to get the time zone right), the root and user password, username "user" / full name "User", the "Partition disks" "Write the changes to disks?" (which defaults to "No"), and to pick a UK debian mirror.  In "Software selection", take only the defaults. Then it reboots to a user login.  Approx 1hr 15 min to get to the "boot the system" 

Don't worry about the warning that pops up earlier on (something about 'probing guessed raw'); it's just QEMU trying to make friends.

Ctrl-A X to terminate QEMU (not "continue to boot into new system").


### Using the installed (vanilla debian) system

Before re-launching QEMU, it's a good idea to remove the Debian .iso so that we don't end up back in the installer if we boot from the CDROM again. The easiest way is simply to remove the last two lines from the QEMU invocation, which gets rid of the emulated CDROM drive entirely. With that gone, you should be able to 
boot the new system and log in with the credentials you specified during installation. 


```
cd $REPOS
qemu-system-aarch64 -M virt \
  -machine virtualization=true -machine virt,gic-version=3    \
  -cpu cortex-a72 -smp 2 -m 4096                              \
  -drive if=pflash,format=raw,file=efi.img,readonly=on        \
  -drive if=pflash,format=raw,file=varstore.img               \
  -drive if=virtio,format=qcow2,file=disk.img                 \
  -device virtio-scsi-pci,id=scsi0                            \
  -object rng-random,filename=/dev/urandom,id=rng0            \
  -device virtio-rng-pci,rng=rng0                             \
  -device virtio-net-pci,netdev=net0                          \
  -netdev user,id=net0,hostfwd=tcp::8022-:22                  \
  -nographic
```
That boots linux to a user login.


You can also SSH in from your x86 machine on port 8022:
```
ssh -p 8022 user@localhost
```


## Running our custom pKVM kernel image in QEMU

Replacing the host kernel can be done by building a Debian kernel package using the bindeb-pkg target exposed by the upstream kernel Makefile. However, this can be a bit of a pain because you have to boot up the old host in order to install the package. For quick prototyping, it's possible to pass a kernel Image directly to QEMU and bypass GRUB entirely:
```
-kernel /path/to/custom/Image -append "earlycon root=/dev/vda2"
```
Isn't that magical?

PS: so that's: 

```
cd $REPOS/qemu-host
qemu-system-aarch64 -M virt                                            \
      -machine virtualization=true -machine virt,gic-version=3         \
      -cpu cortex-a72 -smp 2 -m 4096                                   \
      -drive if=pflash,format=raw,file=efi.img,readonly=on             \
      -drive if=pflash,format=raw,file=varstore.img                    \
      -drive if=virtio,format=qcow2,file=disk.img                      \
      -device virtio-scsi-pci,id=scsi0                                 \
      -object rng-random,filename=/dev/urandom,id=rng0                 \
      -device virtio-rng-pci,rng=rng0                                  \
      -device virtio-net-pci,netdev=net0                               \
      -netdev user,id=net0,hostfwd=tcp::8022-:22                       \
      -nographic                                                       \
      -append "earlycon nokaslr kvm-arm.mode=protected root=/dev/vda2" \
      -kernel $REPOS/linux/arch/arm64/boot/Image
```

Here:

- `nokaslr` turns off address-space randomisation (not sure how that interacts with the `CONFIG_RANDOMIZE_BASE` that we already turned off?) 
- `kvm-arm.mode=protected` (found in a pkvm commit message) to actually enable pKVM.


## Aside: Build for analysis

Previously we have also used the upstream `analysis/el2` branch, which builds a standalone binary of the EL2 executable for analysis purposes. This isn't needed right now. 

The `.S` assembly files now also get DWARF5 debug info, and that seems not to be affected by the above configuration (presumably a bug in the linux build process).  Instead, I hacked it by adding the `-gdwarf-4` to `KBUILD_AFLAGS` in `linux/Makefile`:
```
KBUILD_AFLAGS   := -D__ASSEMBLY__ -fno-PIE -gdwarf-4
```
The analysis/el2 branch by default builds the EL2 files at -O0, for our analysis.  To change, hack -O0 to -O2 in 
`$REPOS/linux/arch/arm64/kvm/hyp/nvhe/Makefile.nvhe`.
