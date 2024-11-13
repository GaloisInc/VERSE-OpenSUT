import functools
import os
import random
import socket
import subprocess
import sys
import threading
import time
import traceback


ALL_TESTS = []

def test(f):
    ALL_TESTS.append(f)
    return f


@test
def test_success_key0(sock):
    sock.send(b'\x00')
    challenge = sock.recv(32)
    assert challenge == b'This challenge is totally random' 
    sock.send(challenge)
    key = sock.recv(32)
    assert key == b'key for encrypting secret things'

@test
def test_success_key1(sock):
    sock.send(b'\x01')
    challenge = sock.recv(32)
    assert challenge == b'This challenge is totally random' 
    sock.send(challenge)
    key = sock.recv(32)
    assert key == b'another secret cryptographic key'

@test
def test_failure_bad_key(sock):
    sock.send(b'\x99')
    challenge = sock.recv(32)
    assert challenge == b'This challenge is totally random' 
    sock.send(challenge)
    key = sock.recv(32)
    # The server should close the connection without sending a key, so we
    # receive zero bytes here.
    assert len(key) == 0

@test
def test_failure_bad_response(sock):
    sock.send(b'\x00')
    challenge = sock.recv(32)
    assert challenge == b'This challenge is totally random' 
    sock.send(b'Invalid reply for that challenge')
    key = sock.recv(32)
    # The server should close the connection without sending a key, so we
    # receive zero bytes here.
    assert len(key) == 0

@test
def test_slow(sock):
    '''Successful test case, but we read and send only 3 bytes at a time.'''
    sock.send(b'\x00')

    challenge = b''
    while len(challenge) < 32:
        time.sleep(0.05)
        b = sock.recv(3)
        assert len(b) > 0, 'unexpected EOF'
        challenge += b
    assert challenge == b'This challenge is totally random' 

    for i in range(0, len(challenge), 3):
        sock.send(challenge[i : i + 3])
        time.sleep(0.05)


    key = b''
    while len(key) < 32:
        time.sleep(0.05)
        b = sock.recv(3)
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

def run_test(test_func, sock, results):
    try:
        test_func(sock)
    except Exception as e:
        results.add((test_func.__name__, e))
    else:
        results.add((test_func.__name__, None))


def main():
    port = random.randrange(48 * 1024, 64 * 1024)
    env = os.environb.copy()
    env[b'MKM_PORT'] = str(port).encode('ascii')
    p = subprocess.Popen('./mkm', env=env)
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
        thread = threading.Thread(target=run_test, args=(test_func, sock, results))
        threads.append(thread)

    random.shuffle(threads)
    for thread in threads:
        thread.start()

    for thread in threads:
        thread.join()

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
