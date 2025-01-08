# adding XMSS
## library downloaded and building 8:30
had to fix a warning
## 42:50
CN can't handle offsetof() in an integer constant expression
after fixing that I get this:
    (debug 0): constructValue_aux: is WRONG for union ==> always assigning the first member
    internal error: TODO: Core_typing, PEmember_shift => struct with flexible array member
## 51:30
after investigation, those are actually two errors! you can ge the first without crashing
## 54:20
no atomics, and also CN doesn't define __STDC_NO_ATOMICS__
## 54:30
cn: internal error, uncaught exception:
    Z.Overflow
    Raised by primitive operation at Z.to_int in file "z.ml", line 221, characters 46-56

haven't tracked it down, probably a u64 or u128 or something
## 1:10:00 tracked it down and filed issue, stopped timing for now
## 1:51:00 more progress cutting down headers, isolated and filed CN #804
## 1:56:00 headers cut down to the point CN can report semantic failures
## 2:27:00 CN warns about not having variables in the invariant even if they are declared later in the function
Understandable given how all variables are hoisted but it should be fixable -- these variables cannot be anything but uninitialized and unreferenceable at this time, unless they're static
this is #254
## 3:26:00 some difficulties with functions that allocate internally not proving they return the region non-null
maybe something about the argument being &x
## 4:00:00 in some situations CN checks assertions in reverse order??? just discovered this and can actually proceed
## 4:33:00 the difficulty was because the code uses an ok = ok && GOOD = f(...) pattern and the first one can fail
CN was exploring the branch where none of those things happen! The test free block does not consider the case where there was any failure. I consider this a sort of bug in some real XMSS code
## 5:00:00 proceeding on adding initial specs for all functions (happy-path only)
## 5:20:00 started working on a signature-check implementation to drop into firmware.c (using previous specs)
## 6:42:00 signature-check implementation specs are valid
## 6:53:00 code verifies as xmss or sha256, but attest is not implemented
