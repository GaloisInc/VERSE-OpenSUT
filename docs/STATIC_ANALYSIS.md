# Static Analysis of OpenSUT components

## Infer

### Installation

Use the OpenSUT base image for development (at least on Mac). Download and install infer with:
```
curl -sSL "https://github.com/facebook/infer/releases/download/v1.2.0/infer-linux-x86_64-v1.2.0.tar.xz" \
| tar -C /opt -xJ && \
ln -s "/opt/infer-linux-x86_64-v1.2.0/bin/infer" /usr/local/bin/infer
```

### Mission Key Management

Found issues with `mission_key_management` in the code that hasn't been CN tested/verified (no issues found with `client.c`):

#### policy.c

Infer:
```
policy.c:108: error: Dead Store
  The value written to `&tmp` is never used. 
  106.     uint8_t hmac_message[MEASURE_SIZE + NONCE_SIZE] = {0};
  107.     // TODO gross hack caused by weird CN type lifting 
  108.     uint8_t *tmp = hmac_message; 
           ^
  109. 
  110.     // TODO Should be automated 
```

#### parser.c

Infer:
```
parser.c:33: error: Dead Store
  The value written to `&p` is never used. 
  31.     p += KEY_ID_SIZE;
  32.     memcpy(entry->key, p, KEY_SIZE);
  33.     p += KEY_SIZE;
          ^
  34.     return 1;
  35. }

```

#### mkm.c

Infer:
```C
#0
mkm.c:137: error: Null Dereference
  `c` could be null (from the call to `client_new()` on line 136) and is dereferenced in the call to `client_epoll_ctl()`. 
  135.                     int sock_client = accept(sock_listen, NULL, 0);
  136.                     struct client* c = client_new(sock_client);
  137.                     ret = client_epoll_ctl(c, epfd, EPOLL_CTL_ADD);
                                 ^
  138.                     if (ret != 0) {
  139.                         perror("epoll_ctl (add)");
```

### Trusted boot

**TL;DR:** Dead stores are not checked by CN. Uninitialized variable and null deref is over-approximated, and thus a false positive with infer
(the specs for CN avoid the condition).

Legitimate issue, fixed by declaring only if `CN_ENV`
```
trusted_boot.c:249: error: Dead Store
  The value written to `&e` is never used.
  247.     SHA256_Init(&ctx);
  248.
  249.     uintptr_t e = (uintptr_t)end_address;
           ^
  250.     uintptr_t s = (uintptr_t)start_address;
  251. #ifndef CN_ENV

trusted_boot.c:250: error: Dead Store
  The value written to `&s` is never used.
  248.
  249.     uintptr_t e = (uintptr_t)end_address;
  250.     uintptr_t s = (uintptr_t)start_address;
           ^
  251. #ifndef CN_ENV
  252.     size_t size = end_address - start_address;

Legitimate issue - should have been caught by CN?
trusted_boot.c:401: error: Dead Store
  The value written to `&hmac_input_0` is never used.
  399.     if (hmac != NULL) {
  400.         uint8_t hmac_input[MEASURE_SIZE + NONCE_SIZE];
  401.         uint8_t *hmac_input_0 = hmac_input;
               ^
  402.         uint8_t *hmac_input_MEASURE_SIZE = &hmac_input[MEASURE_SIZE];
  403.

trusted_boot.c:402: error: Dead Store
  The value written to `&hmac_input_MEASURE_SIZE` is never used.
  400.         uint8_t hmac_input[MEASURE_SIZE + NONCE_SIZE];
  401.         uint8_t *hmac_input_0 = hmac_input;
  402.         uint8_t *hmac_input_MEASURE_SIZE = &hmac_input[MEASURE_SIZE];
               ^
  403.
  404.         /*$ apply SplitAt_Block_u8(hmac_input_0, MEASURE_SIZE()+NONCE_SIZE(), MEASURE_SIZE(), NONCE_SIZE()); $*/

trusted_boot.c:453: error: Dead Store
  The value written to `&buf_0` is never used.
  451.     {
  452.         /*$ assert(total < count); $*/
  453.         uint8_t *buf_0 = (uint8_t*)buf;
               ^
  454.         /*$ extract Block<uint8_t>, (u64)total; $*/
  455.         uint8_t *buf_total = &((uint8_t*)buf)[total];


Found 15 issues (console output truncated to 5, see '/work/components/platform_crypto/shave_trusted_boot/infer-out/report.txt' for the full list)
                      Issue Type(ISSUED_TYPE_ID): #
                          Dead Store(DEAD_STORE): 14
  Uninitialized Value(PULSE_UNINITIALIZED_VALUE): 1
```

### Mission Protection System

can't be build on the OpenSUT base image - Verilator error apparently (looks like there is a mismatch of the verilator versions):

```
/usr/bin/ld: build.no_self_test.x86_64/verilator_build/verilated.cpp.o: in function `VerilatedContext::threadPoolp()':
/usr/share/verilator/include/verilated.cpp:2609:(.text+0xe53c): undefined reference to `VlThreadPool::VlThreadPool(VerilatedContext*, unsigned int)'
``

Also, there seem to be casting problems with `verilator 5.02`:

```
variants/actuation_unit_generated_SystemVerilog.cpp: In function 'uint8_t Actuate_D0_generated_SystemVerilog(uint8_t (*)[4], uint8_t)':
variants/actuation_unit_generated_SystemVerilog.cpp:22:16: error: invalid cast from type 'VlWide<3>' to type 'uint8_t*' {aka 'unsigned char*'}
   22 |         memcpy((uint8_t *)actuate_d0.trips + b, (uint8_t *)trips + (11 - b), 1);
      |                ^~~~~~~~~~~~~~~~~~~~~~~~~~~
variants/actuation_unit_generated_SystemVerilog.cpp: In function 'uint8_t Actuate_D1_generated_SystemVerilog(uint8_t (*)[4], uint8_t)':
variants/actuation_unit_generated_SystemVerilog.cpp:41:16: error: invalid cast from type 'VlWide<3>' to type 'uint8_t*' {aka 'unsigned char*'}
   41 |         memcpy((uint8_t *)actuate_d1.trips + b, (uint8_t *)trips + (11 - b), 1);
      |                ^~~~~~~~~~~~~~~~~~~~~~~~~~~
At global scope:
cc1plus: note: unrecognized command-line option '-Wno-shift-op-parentheses' may have been intended to silence earlier diagnostics
make: *** [Makefile:227: build.no_self_test.x86_64/variants/actuation_unit_generated_SystemVerilog.cpp.o] Error 1
```

### Ardupilot

Unlikely to work, as Ardupilot uses `waf` for building, which infer might not understand - and the build process is very complex.