CN_FLAGS=-I include --include=include/wars.h --magic-comment-char-dollar
CN=cn $(CN_FLAGS)

proofs: components/actuator.cn \
 components/instrumentation_common.cn \
 components/instrumentation.cn \
 components/actuation_unit.cn

%.cn: %.c
	$(CN) $<

components/actuation_unit.cn: components/actuation_unit.c
	$(CN) $< --skip=actuation_logic_collect_trips
