import os
import select
import socket
import subprocess
import time

CONFIG_DIR = os.path.abspath(os.path.dirname(__file__))
VM_RUNNER_DIR = os.path.join(CONFIG_DIR, '../..')
TESTS_DIR = os.path.join(CONFIG_DIR, '../../../../components/mission_protection_system/tests')

def main():
    proc_vm = None
    try:
        rts_socket = os.path.join(VM_RUNNER_DIR, 'serial.socket')

        print('run_tests.py: build application images')
        subprocess.run(
            ('bash', os.path.join(CONFIG_DIR, 'build_img.sh')),
            cwd = VM_RUNNER_DIR,
            check = True,
        )

        print('run_tests.py: build vm_runner')
        subprocess.run(
            ('cargo', 'build'),
            cwd = VM_RUNNER_DIR,
            check = True,
        )

        print('run_tests.py: start VM')
        proc_vm = subprocess.Popen(
            ('cargo', 'run', '--', os.path.join(CONFIG_DIR, 'base_nested.toml')),
            cwd = VM_RUNNER_DIR,
            # Prevent the VM process from intercepting ^C.
            stdin = subprocess.DEVNULL,
        )

        # Wait for VM startup.  We detect startup by listening on the secondary
        # serial port for the MPS to send some output.
        print('run_tests.py: waiting for serial.socket')
        sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        for _ in range(10):
            try:
                sock.connect(rts_socket)
                break
            except OSError:
                pass
            time.sleep(1)
        print('run_tests.py: waiting for data on serial.socket')
        sock.settimeout(300)
        sock.recv(1)
        sock.close()

        # Run the test suite.
        print('run_tests.py: run test suite')
        subprocess.run(
            ('python3', 'run_all.py'),
            cwd = TESTS_DIR,
            env = {
                'RTS_SOCKET': rts_socket,
                'QUICK': '1',
                **os.environ
            },
            check = True,
        )

        # Signal the MPS to shut down.
        print('run_tests.py: shut down MPS')
        sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        sock.connect(rts_socket)
        sock.send(b'Q\r\n')
        sock.close()

        # Wait for the VM to terminate.
        print('run_tests.py: wait for VM to exit')
        proc_vm.wait(timeout = 300)
        assert proc_vm.returncode == 0
        proc_vm = None
    finally:
        if proc_vm is not None and proc_vm.returncode is None:
            proc_vm.kill()

if __name__ == '__main__':
    main()
