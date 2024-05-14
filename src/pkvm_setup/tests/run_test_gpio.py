'''
Test basic GPIO functionality.  This runs QEMU and two helper scripts,
`gpio_test_client.py` (outside the VM) and `gpio_test_vm_script.sh` (inside the
VM), and checks that the two scripts can communicate through an emulated GPIO
device.
'''
import os
import re
import subprocess
import sys

# When using `systemd.run`, output from the script is prefixed with the
# timestamp, the name of the top-level program (in this case "bash"), and the
# PID that produced the output.
BASH_LINE_RE = re.compile(br'\[[0-9. ]+\] bash\[[0-9]+\]: (.*)')


def require(path, desc):
    assert os.path.exists(path), 'missing %r; %s' % (path, desc)

def main():
    tests_dir = os.path.abspath(os.path.dirname(sys.argv[0]))
    pkvm_dir = os.path.dirname(tests_dir)

    proc_vhost = None
    proc_ctrl = None

    try:
        # Start vhost-device-gpio, which implements the virtio GPIO device.
        # QEMU and the external controller script both connect to this.
        vhost_path = os.path.join(pkvm_dir, 'vhost-device/target/debug/vhost-device-gpio')
        require(vhost_path, 'run build_vhost_device.sh first')
        proc_vhost = subprocess.Popen(
            (
                vhost_path,
                '--socket-path', './gpio-qemu.socket',
                # "e4" means an externally controlled GPIO device with 4 lines.
                '--device-list', 'e4',
            ),
            env=dict(
                LD_LIBRARY_PATH = os.path.join(pkvm_dir, 'libgpiod/lib/.libs'),
            ),
        )

        # Start the external controller, `gpio_test_client.py`,  which runs
        # outside the VM.
        ctrl_path = os.path.join(tests_dir, 'gpio_test_client.py')
        proc_ctrl = subprocess.Popen((sys.executable, ctrl_path))

        # Start QEMU, and run `gpio_vm_test_script.sh` inside the VM.
        run_vm_path = os.path.join(pkvm_dir, 'run_vm_common.sh')
        vm_disk_path = os.path.join(pkvm_dir, 'vms/disk_host.img')
        vm_script_path = os.path.join(tests_dir, 'gpio_test_vm_script.sh')
        kernel_path = os.path.join(pkvm_dir, 'vms/pkvm-boot/vmlinuz-pkvm')
        initrd_path = os.path.join(pkvm_dir, 'vms/debian-boot/initrd.img')

        require(vm_disk_path, 'run create_disk_images.sh first')
        require(kernel_path, 'run build_pkvm.sh first')
        require(initrd_path, 'run create_disk_images.sh first')

        # `subprocess.run` waits for completion and just returns the results,
        # not a handle to a running process.
        print('running qemu...')
        result_qemu = subprocess.run(
            (
                '/bin/bash', run_vm_path,
                '-drive', 'if=virtio,format=qcow2,file=%s' % vm_disk_path,
                '-drive', 'if=virtio,format=raw,file=%s' % vm_script_path,
                '-kernel', kernel_path,
                '-initrd', initrd_path,
                '-append', 'earlycon root=/dev/vda2 systemd.run="/bin/bash /dev/vdb"',

                # GPIO-specific args
                '-chardev', 'socket,path=gpio-qemu.socket0,id=vgpio',
                '-device', 'vhost-user-gpio-pci,chardev=vgpio,id=gpio',
                # vhost-user protocol requires that the guest's memory be backed by
                # a file descriptor that it can pass to the vhost-user backend.
                '-object', 'memory-backend-file,id=mem,size=4G,mem-path=/dev/shm,share=on',
                '-numa', 'node,memdev=mem',
            ),
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=60,
        )

        # vhost-device-gpio keeps running, waiting for another connection from
        # QEMU.  Explicitly send SIGTERM to stop it.
        proc_vhost.terminate()

        # Check that the script running inside the VM produced the expected
        # output.
        print('\nQEMU output:')
        saw_pass = False
        for line in result_qemu.stdout.splitlines():
            m = BASH_LINE_RE.match(line.strip())
            if m is None:
                continue
            msg = m.group(1)
            print(msg.decode('utf-8', errors='replace'))
            assert not msg.startswith(b'[FAIL]'), 'saw test failure: %r' % line
            if msg == b'TEST PASSED':
                saw_pass = True
        assert saw_pass, 'missing expected line "TEST PASSED"'

        result_qemu.check_returncode()

        # Other child processes should be done by now.
        proc_ctrl.wait(timeout=1)
        proc_vhost.wait(timeout=1)
    finally:
        proc_vhost.kill()
        proc_ctrl.kill()

if __name__ == '__main__':
    main()
