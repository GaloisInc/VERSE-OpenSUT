SRC = $(wildcard *.c)
OBJ = $(SRC:.c=.o) # Exclude test.o from the object files list
CC = gcc
CFLAGS = -I.

CN_FLAGS=-I . --include=../../include/wars.h --magic-comment-char-dollar
CN=cn $(CN_FLAGS)

trusted_boot: $(OBJ)
	$(CC) $(CFLAGS) -o $@ $^

%.o: %.c
	$(CC) $(CFLAGS) -c $< -o $@

clean:
	rm -f $(OBJ) trusted_boot

cn_proof: trusted_boot.c
	$(CN) $<
