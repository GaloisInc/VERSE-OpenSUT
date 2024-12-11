#pragma once

#include <stdint.h>
#include "policy.h"

enum client_state {
    // Waiting to receive a request for a specific key ID.
    CS_RECV_KEY_ID,
    // In the process of sending a challenge for attestation.
    CS_SEND_CHALLENGE,
    // Waiting to receeive the attestation response.
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
    enum client_state state;
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
// netx to update the epoll event mask.
enum client_event_result client_event(struct client* c, uint32_t events);
