CN_FLAGS=-I include --include=include/wars.h --magic-comment-char-dollar
CN=cn $(CN_FLAGS)

proofs: components/actuator.cn components/instrumentation_common.cn components/instrumentation.cn

%.cn: %.c
	$(CN) $<
