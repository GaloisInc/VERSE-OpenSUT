all: jsbsim_proxy

CFLAGS = -Wall -Wextra -pedantic

jsbsim_proxy: jsbsim_proxy.o
	$(CC) $< -o $@ $(CFLAGS)

jsbsim_proxy.o: jsbsim_proxy.c
	$(CC) -c $< -o $@ $(CFLAGS)

.PHONY: clean
clean:
	rm -f jsbsim_proxy jsbsim_proxy.o
