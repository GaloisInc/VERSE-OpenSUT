Note: if you resize the terminal while the installer is running, the display
might get corrupted.  Press `^A ^A ^L` to redraw it.  (`^A` is the escape
character for QEMU's terminal multiplexer; `^A ^A` sends `^A` to the VM; and
`^A ^L` causes the `screen` instance that `debian-installer` sets up to redraw
its display.)
