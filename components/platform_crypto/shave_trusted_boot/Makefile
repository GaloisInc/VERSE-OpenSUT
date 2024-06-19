F ?=
FRAMAC_FLAGS= -cpp-extra-args="-I ." -wp-split -wp-session /tmp/wp-session -wp-cache /tmp/update -wp-smoke-tests $(F)
FRAMAC=frama-c $(FRAMAC_FLAGS) -wp-rte -wp $(FRAMAC_FLAGS) -wp-prover tip,alt-ergo,z3

CN_FLAGS=-I . --include=wars.h --magic-comment-char-dollar
CN=cn $(CN_FLAGS)

framac_proof:
	$(FRAMAC) firmware.c

cn_proof: firmware.c
	$(CN) $<
