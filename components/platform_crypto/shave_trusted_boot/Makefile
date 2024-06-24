SRC = $(wildcard *.c)
OBJ = $(filter-out test.o, $(SRC:.c=.o)) # Exclude test.o from the object files list
CC = gcc
CFLAGS = -I.

F ?=
FRAMAC_FLAGS= -cpp-extra-args="-I ." -wp-split -wp-session /tmp/wp-session -wp-cache /tmp/update -wp-smoke-tests $(F)
FRAMAC=frama-c $(FRAMAC_FLAGS) -wp-rte -wp $(FRAMAC_FLAGS) -wp-prover tip,alt-ergo,z3

CN_FLAGS=-I . --include=../../include/wars.h --magic-comment-char-dollar
CN=cn $(CN_FLAGS)

# Frama-C proofs currently fail, and the specs are likely incorrect, or
# written for a different (older) version of Frama-C
framac_proof:
	$(FRAMAC) secure_boot.c

cn_proof: secure_boot.c
	$(CN) $<

secure_boot: $(OBJ)
	$(CC) $(CFLAGS) -o $@ $^

%.o: %.c
	$(CC) $(CFLAGS) -c $< -o $@

clean:
	rm -f $(OBJ) secure_boot
