// Client state machine.  Each connection has a separate `struct client`
// object, which tracks progress through the key request protocol for that
// connection.

#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#include <sys/socket.h>
#include <unistd.h>
#include <stdio.h>

//SYSTEM_HEADERS
// ^^^ magic string used during preprocessing - do not move / remove 

# include "client.h" 

#if ! defined(CN_ENV)
# include <sys/types.h>
# include <sys/epoll.h>
#else  
# include "cn_stubs.h"
# include "cn_array_utils.h"
#endif

// TODO `Alloc` construct not supported by `cn test`
#if defined(CN_ENV) && ! defined(CN_TEST) 
# include "cn_memory.h"
#endif 

#if defined(CN_TEST) 
# define NULL ((void *)0)
#endif 

uint32_t client_state_epoll_events(enum client_state state) 
/*$
requires ValidState( state ); 
$*/
{
    switch (state) {
        case CS_RECV_KEY_ID:
            return EPOLLIN;
        case CS_SEND_CHALLENGE:
            return EPOLLOUT;
        case CS_RECV_RESPONSE:
            return EPOLLIN;
        case CS_SEND_KEY:
            return EPOLLOUT;
        case CS_DONE:
            return 0;

        default: { 
            /*$ assert(false); $*/  // <-- Prove this state is unreachable
            return 0;
        } 
    }
}

/*$ 
datatype OptionClientObject {
    SomeClientObject {struct client obj}, 
    NoneClientObject {}
}
predicate (OptionClientObject) OptionClientNew(pointer p, i32 fd, i32 state)
{
    if (is_null(p)) {
        return NoneClientObject {}; 
    } else {
        take Client_out = ClientObject(p);
        assert(Client_out.fd == fd); 
        assert(((i32) Client_out.state) == state); 
        return SomeClientObject { obj: Client_out } ;  
    }
}
$*/

struct client* client_new(int fd) 
/*$ 
ensures take Client_out = OptionClientNew(return, fd, CS_RECV_KEY_ID);
$*/
{
    struct client* c = malloc(sizeof(struct client));
    if (c == NULL) {
        perror("malloc (client_new)");
        return NULL;
    }
    /*$ from_bytes Block<struct client>(c); $*/
    c->fd = fd;
    c->pos = 0;
    c->state = CS_RECV_KEY_ID;
    c->key = NULL;
    memset(c->challenge,0,NONCE_SIZE);
    memset(c->response,0,MEASURE_SIZE + HMAC_SIZE);
    memset(c->key_id,0,KEY_ID_SIZE);
    return c;
}

void client_delete(struct client* c) 
/*$ 
requires take Client_in = ClientObject(c); 
$*/
{
    int ret = shutdown(c->fd, SHUT_RDWR);
    if (ret != 0) {
        perror("shutdown (client_delete)");
        // Keep going.  Even if TCP shutdown fails, we still need to close the
        // file descriptor.
    }
    ret = close(c->fd);
    if (ret != 0) {
        perror("close (client_delete)");
        // Keep going.  On Linux, `close` always closes the file descriptor,
        // but may report I/O errors afterward.
    }
#if defined(CN_ENV) 
    // Ghost code: return ownership of the key 
    key_release(c->key); 
#endif 
    /*$ to_bytes Block<struct client>(c); $*/
    free(c);
}

uint8_t* client_read_buffer(struct client* c) 
/*$ 
requires take Client_in = ClientObject(c); 
ensures take Client_out = ClientObject(c);
        Client_out == Client_in; 
        // TODO ugly notation, should support if-elif-elif-...-else 
        if (((i32) Client_in.state) == CS_RECV_KEY_ID) {
            ptr_eq( return, member_shift(c, key_id) )
        } else { if (((i32) Client_in.state) == CS_RECV_RESPONSE) { 
            ptr_eq( return, member_shift(c, response) )
        } else {
            is_null(return)
        }}; 
$*/
{
    switch (c->state) {
        case CS_RECV_KEY_ID:
            return c->key_id;
        case CS_RECV_RESPONSE:
            return c->response;
        default:
            return NULL;
    }
}

const uint8_t* client_write_buffer(struct client* c) 
/*$ 
requires take Client_in = ClientObject(c); 
ensures take Client_out = ClientObject(c); 
        Client_in == Client_out; 
        if (((i32) Client_in.state) == CS_SEND_CHALLENGE) {
            ptr_eq( return, member_shift(c, challenge) )
        } else { if (((i32) Client_in.state) == CS_SEND_KEY) { 
            // TODO Confusing distinction from the previous case! This is caused 
            // by the fact `challenge` is an array field, and `key` is a value field
            ptr_eq( return, Client_in.key )
        } else {
            is_null(return)
        }}; 
$*/
{
    switch (c->state) {
        case CS_SEND_CHALLENGE:
            return c->challenge;
        case CS_SEND_KEY:
            return c->key;
        default:
            return NULL;
    }
}

size_t client_buffer_size(struct client* c) 
/*$
requires take Client_in = ClientObject(c); 
ensures take Client_out = ClientObject(c); 
        Client_out == Client_in; 
        if (((i32) Client_in.state) == CS_RECV_KEY_ID) { 
            return == KEY_ID_SIZE()
        } else { if ( ((i32) Client_in.state) == CS_SEND_CHALLENGE ) {
            return == NONCE_SIZE()
        } else { if ( ((i32) Client_in.state) == CS_RECV_RESPONSE ) {
            return == MEASURE_SIZE() + HMAC_SIZE()
        } else { if ( ((i32) Client_in.state) == CS_SEND_KEY ) {
            return == KEY_SIZE()
        } else {  
            return == 0u64  // CS_DONE and default cases 
        }}}}; 
$*/
{
    switch (c->state) {
        case CS_RECV_KEY_ID:
            return sizeof(c->key_id);
        case CS_SEND_CHALLENGE:
            return sizeof(c->challenge);
        case CS_RECV_RESPONSE:
            return sizeof(c->response);
        case CS_SEND_KEY:
            return KEY_SIZE;
        case CS_DONE:
            return 0;

        default: { 
            /*$ assert(false); $*/  // <-- Prove this state is unreachable
            return 0;
        } 
    }
}


int client_epoll_ctl(struct client* c, int epfd, int op) 
/*$
// TODO fill in an actual spec here, depending what's needed 
trusted; 
requires
    true; 
ensures 
    true; 
$*/
{
#ifndef CN_ENV
    struct epoll_event ev;
    ev.data.ptr = c;
    ev.events = client_state_epoll_events(c->state);
    return epoll_ctl(epfd, op, c->fd, &ev);
#else
    return 0;
#endif
}


enum client_event_result client_read(struct client* c) 
/*$ 
requires 
    take Client_in = ClientObject(c); 
    let pos = (u64) Client_in.pos; 
ensures 
    take Client_out = ClientObject(c); 
    // TODO more compact notation? 
    Client_out.fd == Client_in.fd; 
    Client_out.challenge == Client_in.challenge; 
    ptr_eq(Client_out.key, Client_in.key);
    Client_out.state == Client_in.state; 

    // TODO Seems like we should be able to prove this
    // Client_out.key_id == Client_in.key_id; 
$*/
{
    uint8_t* buf = client_read_buffer(c);
    if (buf == NULL) {
        // There's no read operation to perform.
        return RES_DONE;
    }

    size_t buf_size = client_buffer_size(c);
    if (c->pos >= buf_size) {
        // Read operation has already finished.
        return RES_DONE;
    }

    // TODO Mysterious why this particular case split is needed
    /*$ split_case(Client_in.state == (u32) CS_RECV_KEY_ID); $*/

    /*$ apply SplitAt_Owned_u8(buf, buf_size, pos, buf_size - pos ); $*/
    /*$ apply ViewShift_Owned_u8(buf, buf + pos, pos, buf_size - pos ); $*/
    int ret = read(c->fd, buf + c->pos, buf_size - (uint64_t) c->pos);
    /*$ apply UnViewShift_Owned_u8(buf, buf + pos, pos, buf_size - pos ); $*/
    /*$ apply UnSplitAt_Owned_u8(buf, buf_size, pos, buf_size - pos ); $*/

    if (ret < 0) {
        perror("read (client_read)");
        return RES_ERROR;
    } else if (ret == 0) {
        return RES_EOF;
    }
    c->pos += ret;

    return c->pos == buf_size ? RES_DONE : RES_PENDING;
}

enum client_event_result client_write(struct client* c) 
/*$ 
requires 
    take Client_in = ClientObject(c); 
    let pos = (u64) Client_in.pos; 
ensures 
    take Client_out = ClientObject(c); 
    Client_out.state == Client_in.state; 
$*/
{
    const uint8_t* buf = client_write_buffer(c);
    if (buf == NULL) {
        // There's no write operation to perform.
        return RES_DONE;
    }

    size_t buf_size = client_buffer_size(c);
    if (c->pos >= buf_size) {
        // Write operation has already finished.
        return RES_DONE;
    }

    // TODO Mysterious why this particular case split is needed
    /*$ split_case(Client_in.state == (u32) CS_SEND_CHALLENGE); $*/

    // TODO Why is this is needed for write() but not read() ?
    // I think this is because of the particular path conditions  
    /*$ extract Owned<uint8_t>, pos; $*/ 

    /*$ apply SplitAt_Owned_u8(buf, buf_size, pos, buf_size - pos ); $*/
    /*$ apply ViewShift_Owned_u8(buf, buf + pos, pos, buf_size - pos ); $*/

    int ret = write(c->fd, buf + c->pos, buf_size - (uint64_t) c->pos);

    /*$ apply UnViewShift_Owned_u8(buf, buf + pos, pos, buf_size - pos ); $*/
    /*$ apply UnSplitAt_Owned_u8(buf, buf_size, pos, buf_size - pos ); $*/

    if (ret < 0) {
        perror("write (client_write)");
        return RES_ERROR;
    } else if (ret == 0) {
        return RES_EOF;
    }
    c->pos += ret;

    return c->pos == buf_size ? RES_DONE : RES_PENDING;
}


void client_change_state(struct client* c, enum client_state new_state) 
/*$ 
requires 
    take Client_in = ClientObject(c); 
    ValidState(new_state); 
    ValidTransition(Client_in.state, new_state); 
ensures 
    take Client_out = ClientObject(c);

    // TODO more compact notation needed saying 'all fields except but X remains unchanged' 
    Client_out.fd == Client_in.fd; 
    Client_out.challenge == Client_in.challenge; 
    ptr_eq(Client_out.key, Client_in.key); 
    Client_out.key_id == Client_in.key_id; 
    Client_out.pos == 0u8; 
    Client_out.state == new_state; 
$*/
{
    c->state = new_state;
    c->pos = 0;
}

enum client_event_result client_event(struct client* c, uint32_t events) 
#if ! defined(CN_TEST) 
// TODO unclear why this isn't handled properly by `cn test`
/*$ accesses __stderr; $*/ 
#endif 
/*$ 
requires 
    take Client_in = ClientObject(c); 
 ensures 
    take Client_out = ClientObject(c); 
    ValidTransition(Client_in.state, Client_out.state); 
$*/
{
    if (events & EPOLLIN) {
        enum client_event_result result = client_read(c);
        if (result != RES_DONE) {
            return result;
        }
    }
    if (events & EPOLLOUT) {
        enum client_event_result result = client_write(c);
        if (result != RES_DONE) {
            return result;
        }
    }

    if (c->pos < client_buffer_size(c)) {
        // Async read/write operation isn't yet finished.
        //
        // This should be unreachable.  `client_event` should only be called
        // when progress can be made on a current async read or write
        // operation, and the call to `client_read`/`client_write` above will
        // return `RES_PENDING` (causing `client_event` to return early) if the
        // operation isn't finished.
        //
        // We return `RES_ERROR` here so that the epoll loop will close the
        // connection.  Since we didn't properly process the events indicated
        // by `events`, presumably some of those events are still ready and
        // will show up again the next time around the epoll loop, at which
        // point we'll fail to handle them again.  Closing the connection
        // prevents this from looping infinitely and wasting CPU.
        return RES_ERROR;
    }

    // The async operation for the current state is finished.  We can now
    // transition to the next state.
    switch (c->state) {
        case CS_RECV_KEY_ID: { // NOTE: additional block needed for declaration 

#if ! defined(CN_ENV)
            memcpy(c->challenge, "random challenge", NONCE_SIZE);
#else 
            // TODO We can't call memcpy with a string argument because CN
            // doesn't support that properly yet. Instead, declare the string as
            // a variable: 
            uint8_t tmp[NONCE_SIZE] = "random challenge"; 
            memcpy(c->challenge, tmp, NONCE_SIZE);
#endif 

            client_change_state(c, CS_SEND_CHALLENGE);
            break; } 
        
        case CS_SEND_CHALLENGE:
            client_change_state(c, CS_RECV_RESPONSE);
            break;

        case CS_RECV_RESPONSE:
#if defined(CN_ENV)
            // Ghost code: return ownership of the key 
            key_release(c->key); 
#endif 
            c->key = policy_match(c->key_id, c->challenge,
                    c->response, c->response + MEASURE_SIZE);
            if (c->key == NULL) {
                // No matching key was found for this request.
                fprintf(stderr, "client %d: error: bad request for key %u\n", c->fd, c->key_id[0]);
                return RES_ERROR;
            }
            client_change_state(c, CS_SEND_KEY);
            fprintf(stderr, "client %d: sending key %u\n", c->fd, c->key_id[0]);
            break;

        case CS_SEND_KEY:
            client_change_state(c, CS_DONE);
            break;

        case CS_DONE:
            // No-op.  This connection is finished, and the main loop should
            // disconnect.
            break;
    }

    return RES_DONE;
}
