#pragma once

#include "policy.h"

enum client_state {
    // Waiting to receive a request for a specific key ID.
    CS_RECV_KEY_ID,
    // In the process of sending a challenge for attestation.
    CS_SEND_CHALLENGE,
    // Waiting to receive the attestation response.
    CS_RECV_RESPONSE,
    // In the process of sending the key.
    CS_SEND_KEY,
    // Protocol finished - no more input or output is expected.
    CS_DONE,
};

enum client_op {
    OP_NONE,
    OP_READ,
    OP_WRITE,
};

struct client {
    int fd;
    // Buffers for async read/write operations.
    uint8_t challenge[NONCE_SIZE];
    uint8_t response[MEASURE_SIZE + HMAC_SIZE];
    const uint8_t* key;
    uint8_t key_id[KEY_ID_SIZE];
    // Read/write position within the current buffer.  Which buffer this refers
    // to depends on the current state.  For the chosen buffer, `buf[i]` is
    // initialized only within the range `0 <= i < pos`.
    uint8_t pos;
#if ! defined(CN_TEST)
    enum client_state state;
#else 
    unsigned int state; 
#endif 
};

enum client_event_result {
    // An error occurred while processing the event.  This could be an I/O
    // error or a protocol-level error.
    RES_ERROR = -2,
    // End of file was reached unexpectedly while processing the event.
    RES_EOF = -1,
    // The event was processed successfully, but some async operation is
    // pending, meaning the protocol is not yet finished.
    RES_PENDING = 0,
    // The event was processed successfully, and the protocol is now complete.
    RES_DONE = 1,
};

struct client* client_new(int fd);
// Deallocate client data.  The client should be removed from epoll before
// calling this.
void client_delete(struct client* c);
// Update the epoll event mask for `c`'s file descriptor to match the pending
// async operation for the current state.  The epoll FD `epfd` and operation
// `op` are passed through directly to `epoll_ctl`.
int client_epoll_ctl(struct client* c, int epfd, int op);
// Process an epoll wakeup with the given event flags.
//
// If this returns `RES_PENDING`, then we may have finished one async operation
// and started a new one, so the caller should next call `client_epoll_ctl`
// next to update the epoll event mask.
enum client_event_result client_event(struct client* c, uint32_t events);

// Either the key is in memory and owned, or the pointer is null 
/*$ 
predicate (map<u64, u8>) KeyPred (pointer p)
  // @PropertyClass: P3-SOP
{
    if (! is_null(p)) { 
        take K = each(u64 i; i < KEY_SIZE()) {Owned<uint8_t>(array_shift<uint8_t>(p,i))}; 
        return K; 
    } else {
        return default< map<u64, u8> >; 
    }
}
$*/ 

// Pure predicate representing valid states of `enum client_state`. 
// CN could easily generate this automatically (see #796) 
/*$
function (boolean) ValidState (u32 state) {
   ((state == (u32) CS_RECV_KEY_ID) || 
    (state == (u32) CS_SEND_CHALLENGE) || 
    (state == (u32) CS_RECV_RESPONSE) || 
    (state == (u32) CS_SEND_KEY) || 
    (state == (u32) CS_DONE) )
}
$*/

// NOTE Wrapper predicate for the allocation record. We distinguish between
// cases because `cn test` doesn't handle Alloc() yet. See
// https://github.com/rems-project/cerberus/issues/776
#if ! defined(CN_TEST)
/*$
predicate (boolean) ClientAlloc (pointer p)
  // @PropertyClass: P3-SOP
{
    take Log = Alloc(p);
    assert ( Log.base == (u64)p );
    assert ( Log.size == sizeof<struct client> );
    return true; 
} 
$*/
#else 
/*$
predicate (boolean) ClientAlloc (pointer p)
{
    return true; 
} 
$*/
#endif

// Predicate representing a valid client object 
/*$
predicate (struct client) ClientObject (pointer p)
  // @PropertyClass: P3-SOP
  // @PropertyClass: P5-UDFunc
{
    take C = Owned<struct client>(p); 
    take Log = ClientAlloc(p); 
    assert ( ValidState(C.state) ) ; 
    take K = KeyPred(C.key); // Discard the key
    return C; 
}
$*/ 

// Pure predicate representing the MKM state machine transitions 
/* 
    start:                  
   ┌────────────────┐       
┌─►│ CS_RECV_KEY_ID ├──────┐
│  └┬─────┬─────────┘      │
└───┘     │                │
   ┌──────▼────────────┐   │
┌─►│ CS_SEND_CHALLENGE ├──►│
│  └┬─────┬────────────┘   │
└───┘     │                │
   ┌──────▼───────────┐    │
┌─►│ CS_RECV_RESPONSE ├───►│
│  └┬─────┬───────────┘    │
└───┘     │                │
   ┌──────▼──────┐         │
┌─►│ CS_SEND_KEY ├────────►│
│  └┬─────┬──────┘         │
└───┘     │                │
   ┌──────▼──┐             │
┌─►│ CS_DONE │◄────────────┘
│  └┬────────┘              
└───┘                       
*/
/*$
function (boolean) ValidTransition (u32 state1, u32 state2) {
       ( state1 == state2 ) 
    || ( (state1 == (u32) CS_RECV_KEY_ID)    && (state2 == (u32) CS_SEND_CHALLENGE) )
    || ( (state1 == (u32) CS_SEND_CHALLENGE) && (state2 == (u32) CS_RECV_RESPONSE)  )
    || ( (state1 == (u32) CS_RECV_RESPONSE)  && (state2 == (u32) CS_SEND_KEY)       )
    || ( ValidState(state1)                  && (state2 == (u32) CS_DONE)           )
}
$*/
