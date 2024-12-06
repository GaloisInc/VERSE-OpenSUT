import functools
import os
import random
import socket
import struct
import subprocess
import sys
import threading
import time
import traceback


ALL_TESTS = []

def test(f):
    ALL_TESTS.append(f)
    return f


KEY_ID_SIZE = 1
KEY_ID_FMT = 'B'
CHALLENGE_SIZE = 32
RESPONSE_SIZE = 32
SECRET_KEY_SIZE = 32


def recv_exact(sock, n):
    buf = bytearray(n)
    uninit = memoryview(buf)
    while len(uninit) > 0:
        amount = sock.recv_into(uninit)
        if amount == 0:
            return bytes(buf)[: len(buf) - len(uninit)]
        uninit = uninit[amount:]
    return bytes(buf)

class MKMClient:
    def __init__(self, sock):
        self.sock = sock

    def send_key_id(self, key_id):
        msg = struct.pack(KEY_ID_FMT, key_id)
        assert len(msg) == KEY_ID_SIZE
        self.sock.sendall(msg)

    def recv_challenge(self):
        return recv_exact(self.sock, CHALLENGE_SIZE)

    def send_response(self, response):
        assert len(response) == RESPONSE_SIZE
        self.sock.sendall(response)

    def recv_key(self):
        return recv_exact(self.sock, SECRET_KEY_SIZE)


@test
def test_success_key0(client):
    client.send_key_id(0)
    challenge = client.recv_challenge()
    assert challenge == b'This challenge is totally random', \
            'bad challenge %r' % (challenge,)
    client.send_response(challenge)
    key = client.recv_key()
    assert key == b'key for encrypting secret things'

@test
def test_success_key1(client):
    client.send_key_id(1)
    challenge = client.recv_challenge()
    assert challenge == b'This challenge is totally random' 
    client.send_response(challenge)
    key = client.recv_key()
    assert key == b'another secret cryptographic key'

@test
def test_failure_bad_key(client):
    client.send_key_id(99)
    challenge = client.recv_challenge()
    assert challenge == b'This challenge is totally random' 
    client.send_response(challenge)
    key = client.recv_key()
    # The server should close the connection without sending a key, so we
    # receive zero bytes here.
    assert len(key) == 0

@test
def test_failure_bad_response(client):
    client.send_key_id(0)
    challenge = client.recv_challenge()
    assert challenge == b'This challenge is totally random' 
    client.send_response(b'Invalid reply for that challenge')
    key = client.recv_key()
    # The server should close the connection without sending a key, so we
    # receive zero bytes here.
    assert len(key) == 0

@test
def test_slow(client):
    '''Successful test case, but we read and send only 3 bytes at a time.'''
    client.send_key_id(0)

    challenge = b''
    while len(challenge) < CHALLENGE_SIZE:
        time.sleep(0.05)
        b = client.sock.recv(3)
        assert len(b) > 0, 'unexpected EOF'
        challenge += b
    assert challenge == b'This challenge is totally random' 

    response = challenge
    for i in range(0, len(response), 3):
        client.sock.send(response[i : i + 3])
        time.sleep(0.05)

    key = b''
    while len(key) < SECRET_KEY_SIZE:
        time.sleep(0.05)
        b = client.sock.recv(3)
        assert len(b) > 0, 'unexpected EOF'
        key += b
    assert key == b'key for encrypting secret things' 


class TestResults:
    def __init__(self):
        self.results = []
        self.lock = threading.Lock()

    def add(self, x):
        with self.lock:
            self.results.append(x)

    def get(self):
        return self.results

def run_test(test_func, client, results):
    try:
        test_func(client)
    except Exception as e:
        results.add((test_func.__name__, e))
    else:
        results.add((test_func.__name__, None))


def main():
    port = random.randrange(48 * 1024, 64 * 1024)
    env = os.environb.copy()
    env[b'MKM_PORT'] = str(port).encode('ascii')
    p = subprocess.Popen('./mkm', env=env)
    try:
        # Delay to let the subprocess start up and listen on the port.  It would be
        # better to monitor `p.stderr` for the "Listening..." log output, but
        # that's more complicated to set up.
        time.sleep(0.1)

        results = TestResults()

        # Open all sockets first, then start the threads.  This implicitly tests
        # that the server can handle multiple simultaneous connections.
        threads = []
        for test_func in ALL_TESTS:
            sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            sock.connect(('localhost', port))
            client = MKMClient(sock)
            thread = threading.Thread(target=run_test, args=(test_func, client, results))
            threads.append(thread)

        random.shuffle(threads)
        for thread in threads:
            thread.start()

        for thread in threads:
            thread.join()
    finally:
        p.terminate()
        try:
            p.wait(timeout=15)
        except subprocess.TimeoutExpired:
            p.kill()

    print()
    all_ok = True
    for name, ex in results.get():
        if ex is None:
            print('%s: OK' % name)
        else:
            print('%s: %s: %s' % (name, type(ex).__name__, ex))
            traceback.print_exception(ex)
            all_ok = False

    if not all_ok:
        sys.exit(1)

if __name__ == '__main__':
    main()
