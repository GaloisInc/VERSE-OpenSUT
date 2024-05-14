'''
Helper script for `run_test_gpio.py`.  This runs outside the VM.  When the VM
manipulates its GPIO output lines, this script responds by adjusting the
inputs.
'''
import select
import socket
import struct
import sys


def iter_messages(sock):
    while True:
        recv_buf = sock.recv(4096)
        for i in range(0, len(recv_buf), 2):
            line = recv_buf[i]
            value = recv_buf[i + 1]
            if value == 255:
                value = -1
            yield line, value
            print('output: %d = %d' % (line, value))

def main():
    sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    sock.connect('./gpio.socket')

    def set_value(line, value):
        sock.send(struct.pack('BB', line, value))

    state = 0
    for line, value in iter_messages(sock):
        if line == 0 and value == 1:
            # Each time the VM outputs 1 on line 0, step through various states
            # for the other lines.
            print('got signal in state %d' % state)
            if state == 0:
                # 1, 0, 0
                set_value(1, 1)
            elif state == 1:
                # 0, 1, 0
                set_value(1, 0)
                set_value(2, 1)
            elif state == 2:
                # 0, 0, 1
                set_value(2, 0)
                set_value(3, 1)
            elif state == 3:
                # 0, 0, 0
                set_value(3, 0)
            elif state == 4:
                # 1, 1, 1
                set_value(1, 1)
                set_value(2, 1)
                set_value(3, 1)
                return
            state += 1

if __name__ == '__main__':
    main()
