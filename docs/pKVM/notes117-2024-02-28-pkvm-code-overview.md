# pKVM code overview

Kayvan Memarian, Ben Simner, Peter Sewell, 2024-03-01

This is a working note; please do not distribute it publicly. 

## Introduction

This note, `notes117-2024-02-28-pkvm-code-structure.md`, gives a quick
introduction to pKVM and its code structure, as a summary for those interested in pKVM
verification. 

This is an update of our earlier notes (especially
`notes37-2020-11-25-pkvm-code-overview`,
`notes068-2022-05-08-pkvm-code-files.md`,
`notes069-2022-05-04-pkvm-state.md`,
`notes070-2022-05-05-pkvm-api.md`).  
It's surely imperfect - some
parts aren't updated, and in any case the code continues to change.
It's based on our reading of the source and some discussion with the developers, 
but this is our understanding, not the developers' own documentation. 

There is some documentation by the developers at 
<https://android-kvm.googlesource.com/linux/+/refs/tags/pkvm-core-6.4/Documentation/virt/kvm/arm/pkvm.rst>.


We have a separate note,
`notes019-2020-06-26-pkvm-build`,
explaining how to build and run pKVM. 


## Repos

The Android source repo is <https://android-kvm.googlesource.com/linux>.  The development team work in a complex collection of branches and patches, assembling them for each Android release. 

Our verification work to date does not track that in detail - instead, we have so far worked from specific snapshots, updated only occasionally.  Our working fork of the Android repo is <https://github.com/rems-project/linux>, with the main branches:

- `pkvm-core-6.4` - the base upstream version that we're currently working above, from the eponymous branch of <https://android-kvm.googlesource.com/linux>
- `pkvm-verif-base-6.4` - this is `pkvm-core-6.4` plus Cambridge hacks for printing from EL2 and increasing EL2 stack size
- `pkvm-verif-6.4` - the working version for our C executable spec (based on top of `pkvm-verif-base-6.4`)
- `hyp-proxy` - this is `pkvm-core-6.4` plus a patch by Thibaut Pérami, which enables EL0 to do hypercalls for testing purposes
- `pkvm-verif-6.4+hyp-proxy` - this is the executable spec (`pkvm-verif-6.4`) plus Thibaut's `hyp-proxy` patch (CAUTION: this is meant as an example; we do not keep it in sync with `pkvm-verif-6.4`)
- `pkvm-verif-cn-bv` - the working version for CN proof


## Motivation for pKVM in Android

pKVM is the foundation of the Android Virtualization Framework, which _"provides secure and private execution environments for executing code. AVF is ideal for security-oriented use cases that require stronger, even formally verified, isolation assurances over those offered by Android's app sandbox"_. The main goal of AVF is to _"provide a secure and private execution environment for next-generation use cases"_; it was first introduced in Android 13, and the intention is that it be deployed in all Android devices.

The development of pKVM is a response to the fact that mobile devices are handling increasing bodies of sensitive data, creating a large incentive for attackers to exploit vulnerabilities, and the existing protection mechanisms are based on Linux kernel process isolation and thus rely on a large trusted computing base (TCB), the 20+ million lines of code of the Linux kernel. The inevitable exploitable vulnerabilities in the TCB thus expose all that sensitive data.

In contrast, the controlled isolation that pKVM aims to provide should depend only on the correctness of the pKVM hypervisor code and its initial setup, so that later flaws or compromises of the Android Linux kernel or other components cannot arbitrarily corrupt the whole system.
pKVM supports protected virtual machines: isolated execution environments running in parallel with the Android linux kernel. 

![Android Virtualization Framework architecture diagram](https://source.android.com/static/docs/core/virtualization/images/architecture1.png)

AVF architecture, from [Android Virtualization Framework](https://source.android.com/docs/core/virtualization)

pKVM  is written in C and assembly as part of the Android Linux codebase. The trusted computing base is much smaller than that of the Linux kernel as a whole: tens of thousands of lines of code rather than tens of millions. This makes it more tractable for conventional engineering than the entire Linux kernel, but it remains challenging: this is low-level concurrent systems C code -- and conventional engineering still cannot provide high assurance of the absence of exploitable bugs.


## Top-level design

For earlier public high-level descriptions of the goals and design, 
see [Android Virtualization Framework](https://source.android.com/docs/core/virtualization),
Will Deacon's 2020-10 KVM Forum slides:
<https://mirrors.edge.kernel.org/pub/linux/kernel/people/will/slides/kvmforum-2020-edited.pdf>,
and this LWN article: <https://lwn.net/Articles/836693/>.


The Arm-A architecture supports multiple _exception levels_, including:

- EL0, for user processes
- EL1, for operating system kernels, e.g. the Android Linux kernel
- EL2, for hypervisors, e.g. pKVM
- EL3, for secure monitor code, e.g. device-specific firmware

pKVM enforces protection by managing address translation.  For code running at EL1 or EL0 (i.e. in the EL1&0 regime),
the Arm-A architecture supports two stages of address translation:

- Stage 1: from _virtual address_ (VA) to _intermediate physical address_ (IPA), controlled by OS code at EL1
- Stage 2: from _intermediate physical address_ (IPA) to _physical address_ (PA), controlled by pKVM code at EL2

For pKVM's own code, which is running at EL2, the architecture has only one stage of translation:

- Stage 1: from _virtual address_ (VA) to _physical address_ (PA), controlled by the pKVM code at EL2

(The architecture reuses the term "Stage 1" in both these two different translation regimes.)

(Arm-A also supports other exception levels, e.g. "Secure EL2", and other translation regimes, but they are not especially relevant here.)

pKVM is a hypervisor running at EL2, with Linux (Android) as one
guest running at EL1. 
This "primary guest" is typically referred to as the _host_ (not to be
confused with the "host machine").
Other critical services can run as other guests at EL1, mutually protected from each other and from the Linux kernel. 

<!-- OMIT THIS DESCRIPTION OF INITIALISATION FOR NOW * (in the normal pKVM use case) initially the machine starts at EL2, eventually reaching the normal linux boot process (head.S)
* while still at EL2, linux prepares the memory for initialising pKVM (EL2 sysregs, vector table, and loads the nvhe code)
* then linux drops to EL1 and continue with the normal linux boot process
* then at some point (while at EL1) linux decides to initialise pKVM by doing a hypercall (`__pkvm_init`), this executes the previous loaded EL2 code, which does
the first time setup of the hypervisor:
    * setup the early allocator
    * setup the Stage 1 page table of pKVM (enables it)
    * creates, but does NOT swithc to, the Stage 2 page table of the host (which is EMPTY)
    * places the normal pKVM trap handlers in the EL2 vector table
    * then returns back to Linux at EL1 (which then continues its boot process)

* eventually linux will call prot_finalise (this is a hypercalls) from all physical CPUs. After all CPUs have done so, pKVM is now fully initialised and in control of EL2
   - "thereafter use to provide controlled isolation between Linux and other guests"



System startup initially follows the normal path to boot Linux, were executions starts at EL2.  The EL2 state is setup and the
EL2 vector table is configure to point to pKVM initial entry point, the execution then goes down to EL1 and continue the normal
Linux boot process.  Then at a certain point Linux (running at EL1) sets up an initial
state for pKVM and transfers control to it at EL2; pKVM then takes
control of its own memory and creates Stage 2 address translations
which it will thereafter use to provide controlled isolation between Linux
and other guests.  It constructs: -->

System startup initially follows the normal path to boot Linux, but
then at a certain point Linux (running at EL1) sets up an initial
state for pKVM and transfers control to it at EL2; pKVM then takes
control of its own memory, creating a Stage 1 mapping for itself, and creates Stage 2 address translations
which it will thereafter use to provide controlled isolation between Linux
and other guests.

--

The basic security property that pKVM enforces is isolation between the host and all the guests (and between those and pKVM itself).  It achieve this by enforcing
that the ranges of all those page tables are disjoint (modulo devices and explicitly shared pages).

The host and guests can interact with pKVM through a small API comprising hypercalls and memory aborts.

Abstractly there are hypercalls to do the following:

- share host pages with pKVM
- create a new guest VM
- destroy a guest VM
- donate pages to a guest
- context switch from host to a guest (Linux does scheduling, not pKVM)
- share guest pages with the host
- and handle PSCI and other functionality

More precisely, these are the key hypercalls that the host can issue (described in detail later):

  * `__pkvm_host_share_hyp`
  * `__pkvm_host_unshare_hyp`
  * `__pkvm_host_reclaim_page`
  * `__pkvm_host_map_guest`
  * `__kvm_vcpu_run`
  * `__pkvm_init_vm`
  * `__pkvm_init_vcpu`
  * `__pkvm_teardown_vm`
  * `__pkvm_vcpu_load`
  * `__pkvm_vcpu_put`

And for guests:

  * `mem_share`
  * `mem_unshare`

pKVM also handle all memory (instruction and data) aborts and all interrupts while the host or guests are running. Scheduling is done by the host, which calls pKVM to do context switching.

For memory aborts by the host, pKVM does mapping on demand of the Stage 2 page table.

The Linux/pKVM interface is based on virtio, with PSA-FF used for the pkvm-interposed secure firmware calls ([PSA-FF](https://developer.arm.com/documentation/den0077/latest),
previously known as the  Secure Partition Client Interface (SPCI)).

In the code, the pKVM-specific entities are mostly named `nvhe`. 
KVM previously existed in two variants, one that used the Armv8.1-A
Virtualization Host Extensions and one that did not, and pKVM is an
adaption of the latter.

## The pKVM state (viewed abstractly)

The state that pKVM manages when handling host/guest hypercalls and aborts consists of:

* a Stage 1 page table, for pKVM's own code (which is running at EL2)
* for each guest, a set of vCPUs (each with their own register state), and a single Stage 2 page table shared by all vCPUs.
* a Stage 2 page table for the host, which is running at EL1&0. This page table is an identity mapping. Initially it is empty; it gets mapped on demand by pKVM (through host memory abort).
  Invalid entries in the host page table encode which entity (pKVM, host, or a guest) has ownership of the physical memory that this entry would be mapping.
* a mapping from opaque identifiers (called `handle`s) to guests.

The concrete state contains C data structures for all of the above as well as allocators and refcounts and suchlike.


## The host and guest interfaces to pKVM

The host and guests interact with pKVM by raising Arm architecture exceptions (from EL1), explicitly with `HVC` hypervisor calls (and `SMC` secure monitor calls),
and implicitly when their Stage 2 address translation faults, or when an interrupt or external abort occurs.  These cause the running hardware thread to switch exception level
to EL2 and jump to the exception vector table whose address is in the EL2 exception vector base address register `VBAR_EL2` (actually to an offset within that table depending on the kind of exception).
After pKVM has done its work, it will return to EL1 with an `ERET` instruction - either to the caller or, in some cases after switching context, to another guest or to the host. 

### The host API

When the host is executing (after pKVM initialisation), the Arm EL2 exception vector base address register `VBAR_EL2` contains the address of the `host.S:__kvm_hyp_host_vector` vector table.
Hypercalls and memory aborts switch the exception level from EL1 to EL2 and begin executing from the `host_el1_sync_vect` entry of this vector table.
This entry saves the host registers (to restore when returning to the host later), and calls the C function `hyp-main.c:handle_trap`, which then dispatches to one of:

- `handle_host_hcall` for hypercalls, as listed in the `hyp-main.c:host_hcall[]` array of function pointers
- `handle_host_mem_abort` (in `mem_protect.c`) for Stage 2 address translation faults
- `handle_host_smc` for calls to the secure monitor - we'll ignore for now.
- `fpsimd_host_restore` - we'll ignore for now

#### Host hypercalls

After pKVM initialisation, the available host hypercalls are:

```
                            // main body in:
__pkvm_host_share_hyp       // nvhe/mem_protect.{h,c}                share one page of memory currently exclusively owned by the host with pKVM
__pkvm_host_unshare_hyp     // ...                                   undo a previous sharing with pKVM of a host page

__pkvm_init_vm              // nvhe/pkvm.c                           create a new VM - create a EL2 copy of a host C data structure configuring a VM state, implicitly donating memory from the host to pKVM to store this copy, returning a fresh VM handle
__pkvm_teardown_vm          // ...                                   destroy a VM - donates back to the host the memory used to hold the EL2 copy of the VM state, and marks any physical memory explicitly given by the host to the guest (so that it can be reclaimed later)

__pkvm_vcpu_load            // hyp-main.c:handle___pkvm_vcpu_load    pin a vCPU of a VM (given its handle) to the current physical CPU
__pkvm_vcpu_put             // hyp-main.c:handle___pkvm_vcpu_put     unpin the vCPU loaded in the current physical CPU

__kvm_vcpu_run              // nvhe/switch.c                         switch the execution of the current physical CPU (away from the host) to the currently pinned (guest) vCPU. This hypercall will return to the host once the guest is interrupted (e.g. on a guest hypercall, a guest memory abort, or a timer interrupt, and so on)

__pkvm_host_donate_guest    // ...                                   donates one page of host memory to the guest of the vCPU pinned to the current physical CPU
__pkvm_host_reclaim_page    // ...                                   potentially zeroes a page, which was previously marked a __pkvm_teardown_vm call, and gives it back to the host

```

For some of these, the `handle_` function in `hyp-main.c` is just a wrapper around a main body, while for others the `handle_` function does the work. 
They get given a `struct kvm_cpu_context *host_ctxt` and pull some host-register arguments out.

#### Host memory aborts

Host memory aborts are handle by `hyp-main.c:handle_host_mem_abort`, which tries to extend the Stage 2 identity mapping for the host for the location that caused the abort.
If the host does not own that location, it injects a fake memory abort into EL1.
In both cases, execution returns to the host, either to retry the memory access that caused the abort, or to the EL1 memory abort exception handler.


### The guest API

When switching to a guest, pKVM sets the exception vector base address register `VBAR_EL2` of the current physical CPU so that when an exception happens during the upcoming execution of a guest, the return to EL2 bring the execution to the pKVM code for handling guest exceptions.

<!-- When switching to a guest, in `switch.c:__kvm_vcpu_run`, it calls `__activate_traps` to set the exception vector base address register `VBAR_EL2` to the per-(physical?)-cpu `__this_cpu_read(kvm_hyp_vector)`.  That seems to be set by `mm.c:pkvm_cpu_set_vector` with some anti-spectre finangling; in the simple case it's just set to `hyp-entry.S:__kvm_hyp_vector`.

The `hyp-entry.S` `el1_sync` table entry branches to `el1_trap` and thence to `entry.S:__guest_exit`, which saves registers and does a `ret`.    That (I think - check) takes us back to the `switch.c:__kvm_vcpu_run`  run loop, which calls `switch.h:fixup_guest_exit` (this will "Return true when we were able to fixup the guest exit and should return to the guest, false when we should restore the host state and return to the main run loop").  Ignoring lots of SError plumbing, this calls `switch.h:kvm_hyp_handle_exit` which picks a handler array based on the `vcpu` and takes a handler `fn` from it. 
The handler arrays are in `switch.c`, either `pvm_exit_handlers` if `vcpu_is_protected(vcpu)` or `hyp_exit_handlers` otherwise (we ignore the non-protected case?). The former has: -->

``` c
  [ESR_ELx_EC_HVC64]       = kvm_handle_pvm_hvc64,        // in pkvm.c
  [ESR_ELx_EC_SYS64]       = kvm_handle_pvm_sys64,        // in switch.c, "for protected VM MSR, MRS or System instruction execution in AArch64"
  [ESR_ELx_EC_SVE]         = kvm_handle_pvm_restricted,   // in sys_regs.c
  [ESR_ELx_EC_FP_ASIMD]    = kvm_hyp_handle_fpsimd,       // in switch.c, "for protected floating-point and Advanced SIMD accesses"
  [ESR_ELx_EC_IABT_LOW]    = kvm_hyp_handle_iabt_low,     // in switch.h, for instruction memory abort
  [ESR_ELx_EC_DABT_LOW]    = kvm_hyp_handle_dabt_low,     // in switch.h, for data memory abort
  [ESR_ELx_EC_WATCHPT_LOW] = kvm_hyp_handle_watchpt_low,  // in switch.h
  [ESR_ELx_EC_PAC]         = kvm_hyp_handle_ptrauth,      // in switch.h
```

#### The guest hypercalls

The `pkvm.c:kvm_handle_pvm_hvc64` dispatches:

```C
    case ARM_SMCCC_VERSION_FUNC_ID:                          // boring
    case ARM_SMCCC_VENDOR_HYP_CALL_UID_FUNC_ID:              // ...
    case ARM_SMCCC_VENDOR_HYP_KVM_FEATURES_FUNC_ID:          // ...
    case ARM_SMCCC_VENDOR_HYP_KVM_HYP_MEMINFO_FUNC_ID:       // ...
    case ARM_SMCCC_VENDOR_HYP_KVM_MEM_SHARE_FUNC_ID:         // share a page with the host - calls pkvm.c:pkvm_memshare_call(vcpu, exit_code) which calls mem_protect.c:__pkvm_guest_share_host, and return to the host upon success
    case ARM_SMCCC_VENDOR_HYP_KVM_MEM_UNSHARE_FUNC_ID:       // unshare a page with the host - calls pkvm.c:pkvm_memunshare_call(vcpu) which calls mem_protect.c:__pkvm_guest_unshare_host, and return to the host upon success
    default:                                                 // calls pkvm.c:pkvm_handle_psci(vcpu) which does real work for some (eg pvm_psci_vcpu_on/off) and passes others to the host
```

#### guest mem aborts

These cause the execution to return to the host, ending the current `__kvm_vcpu_run` call, and returning a description of the aborts.


### Usage of the host and guest interfaces to pKVM

The above interfaces are in a sense internal to Android Linux - they are used directly by Linux kernel code, not by user code, e.g. when the kernel requests that pKVM creates a new virtual machine, or that pKVM context switches from one virtual CPU to another.
However, from a security and verification point of view, they are primary: our specification and the desired security properties are with respect to the behaviour at these interfaces, and the security properties should be maintained for arbitrary sequences of hypercalls and other exceptions. 

(TODO: add brief descriptions of the sequences of hypercalls and other exceptions involved in each of the following)

**Host memory abort**

**Creation of a new VM**

**Context switch**

**Guest memory abort**

**Teardown of a VM**



## Source files

The main pKVM sources are in the following directories:
```
arch/arm64/kvm/hyp/nvhe/    the pKVM-specific EL2 sources.
arch/arm64/kvm/hyp/         code shared between KVM and pKVM, including `pgtable.c` for manipulating page-tables.
arch/arm64/kvm/             the hypervisor and the host/kernel handlers (for both KVM and pKVM).
arch/arm64/include/         many Arm-specific header files
```


Key files include:
```
arch/arm64/kvm/hyp/nvhe/setup.c              pKVM initialisation and handover from Linux
arch/arm64/kvm/hyp/nvhe/mm.c                 construction of pKVM's memory mappings during initialisation, and other bits
arch/arm64/kvm/hyp/nvhe/hyp-init.S           exception vector used transiently during initialisation 

arch/arm64/kvm/hyp/nvhe/host.S               exception vector used for host execution
arch/arm64/kvm/hyp/nvhe/hyp-main.c           host exception handling and host HVC dispatch 

arch/arm64/kvm/hyp/hyp-entry.S               exception vector used for guest execution
arch/arm64/kvm/hyp/entry.S                   guest entry/exit

arch/arm64/kvm/hyp/nvhe/mem_protect.c        host and guest stage 2 management
arch/arm64/kvm/hyp/pgtable.c                 generic pagetable manipulation code (used by mm.c and mem_protect.c in pKVM, and by KVM)
arch/arm64/include/asm/kvm_pgtable.h         the kvm_pte_t and kvm_pgtable_walker types

arch/arm64/kvm/hyp/nvhe/pkvm.c               shadow VM and VCPU management, and guest HVC dispatch
arch/arm64/kvm/hyp/nvhe/switch.c             context switching between guest and host, the guest run-loop, and guest exit handler

arch/arm64/kvm/hyp/nvhe/early_alloc.c        the simple allocator used during pKVM initialisation
arch/arm64/kvm/hyp/nvhe/page_alloc.c         the buddy allocator used for managing page-table pages

arch/arm64/kvm/pkvm.c                        the untrusted EL1 Host code that calls pKVM from Linux
arch/arm64/kvm/arm.c                         the untrusted EL1 Host code that calls pKVM from Linux

arch/arm64/include/linux/kvm_host.h          a lot of the shared KVM/pKVM types for host-controlled information, e.g. `kvm` and `kvm_vcpu`

arch/arm64/kvm/hyp/include/nvhe/spinlock.h   a ticket spinlock

arch/arm64/kvm/hyp/nvhe/tlb.c                TLB maintenance instructions
arch/arm64/kvm/hyp/nvhe/cache.S              data cache clean and instruction cache invalidate
arch/arm64/kvm/hyp/nvhe/sysreg-sr.c          system register save and restore
arch/arm64/kvm/hyp/nvhe/timer-sr.c           timer save and restore

arch/arm64/kvm/hyp/nvhe/hyp.lds{.S}          linker script
arch/arm64/kvm/hyp/nvhe/gen-hyprel.c         standalone program used in build to generate kernel/hyp relocations 

linux/include/linux/types.h                  generic Linux data structure declarations, including the linked list `list_head`
linux/include/linux/list.h                   generic Linux circular doubly linked lists

```

The code refers to - but perhaps only uses parts of - a great many other include files. 


## Concrete state of the pKVM code

The main parts of pKVM's runtime state are:

- the EL2 system registers that control pKVM's own mapping, the Stage 2 mappings, and the targets of exceptions from the host and guests. 
- pKVM's own mapping (`nvhe/mm.c` `struct kvm_pgtable pkvm_pgtable`, protected by `hyp_spinlock_t pkvm_pgd_lock`). This is set up during pKVM initialisation. Most of it is then constant, but it can be changed by host HVCs to share and unshare pages with pKVM.
- pKVM's code, read-only data, globals, per-hardware-CPU variables, and per-hardware-CPU stacks.   These are used for pKVM's own execution.  In particular, while a CPU is running a guest, the per-CPU stack holds the context to come back to.
- pKVM's early allocator (used just during pKVM initialisation) and buddy allocator (used thereafter with various memory pools for managing the memory used for page tables).  This is used only for pKVM's own memory; pKVM doesn't manage memory allocation for the host or guests.
- pKVM's metadata for the host, especially its Stage 2 mapping for the host (`nvhe/mem_protect.c` `struct host_kvm host_kvm`, where that struct type is defined in `mem_protect.h`,  including its pagetable `host_kvm->pgt` and protecting lock `hyp_spinlock_t host_kvm->lock`). This page table is initially empty then is mapped on demand when Stage 2 page faults trap into pKVM. It also records (in annotations in invalid entries) which pages are reserved for pKVM and so should not be mapped here, and (in software-defined flag bits) some owned/shared status.  It's an identity map. 
- pKVM's metadata for guest VMs and their vcpus, especially the per-VM Stage 2 mappings. 

    - The per-VM metadata is in the `pkvm.c:static struct pkvm_hyp_vm **vm_table` (protected by the `pkvm.c:vm_table_lock` spinlock), for which `setup.c` allocates space for an array of `KVM_MAX_PVMS` structs.  
    - Each `struct pkvm_hyp_vm` (defined in `arch/arm64/kvm/hyp/include/nvhe/pkvm.h`) contains a `struct kvm_pgtable pgt` and associated `arch`, `mm_ops`, `pool`, and `lock`.
    - The page table for a VM is set up on VM creation by the `__pkvm_init_vm` hypercall. It's not mapped on demand by pKVM (faults get reported to the host, that can then donate pages).  The guest can share and unshare pages with the host, and the host can donate pages to a guest. 
    - Each of those `struct pkvm_hyp_vm` has a per-vcpu array `struct pkvm_hyp_vcpu *vcpus[]`, each of which has a `struct kvm_vcpu vcpu` (defined in `include/linux/kvm_host.h`) and a pointer back to currently pinned vCPU `struct pkvm_hyp_vcpu **loaded_hyp_vcpu` (when pinned). 


## The build and linking

The pKVM code that runs at EL2 is built, as part of the Linux kernel build, by `arch/arm64/kvm/hyp/nvhe/Makefile`.  This builds an object file `kvm_nvhe.o` that is linked into the final `vmlinux` - though after initialisation it essentially does not share code or data with the linux kernel, that is then running at EL1 encapsulated by the host Stage 2 address translation managed by pKVM.   

During boot, the EL2 code is relocated; it's also mutated to resolve instances of the Linux "alternatives" mechanism, for hardware processor-instance-specific patching. 


## C Carver tooling

The pKVM sources are intertwined with the Linux kernel, using Linux kernel header files and some common C files (including e.g. the `pgtable.c` page-table manipulation code, which is shared with KVM).  For more convenient verification work, our C tree carver tooling <https://github.com/rems-project/c-tree-carver> can be used to pull out just the parts that are needed for pKVM - cutting out the relevant files and the relevant pieces of those files. 


## Testing infrastructure

Normal interaction with pKVM is via the code within the Linux kernel and other guests running at EL1; the hypercall (and other exception) interfaces described above are not exposed to user code running at EL0.  But for testing, and especially testing with arbitrary sequences of hypercalls (not just well-behaved ones), it is useful to be able to directly invoke them from EL0, and have testing infrastructure as user code there.

The `hyp-proxy` patch <https://github.com/rems-project/linux/tree/hyp-proxy> lets one make hypercalls indirectly from EL0, and we have testing infrastructure to conveniently script and run tests above that. 
