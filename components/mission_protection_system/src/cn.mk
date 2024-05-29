CN_FLAGS=-I include --include=include/wars.h --batch
CN=cn $(CN_FLAGS)

proofs: actuator_proof

.PHONY: actuator_proof
actuator_proof: components/actuator.c
	$(CN) $<
