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
            print('got signal in state %d' % state)
            if state == 0:
                set_value(1, 1)
            elif state == 1:
                set_value(1, 0)
                set_value(2, 1)
            elif state == 2:
                set_value(2, 0)
                set_value(3, 1)
            elif state == 3:
                set_value(3, 0)
            elif state == 4:
                set_value(1, 1)
                set_value(2, 1)
                set_value(3, 1)
                return
            state += 1

if __name__ == '__main__':
    main()
