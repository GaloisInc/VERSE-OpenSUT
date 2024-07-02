CN_FLAGS=-I include --include=include/wars.h --magic-comment-char-dollar
CN=cn $(CN_FLAGS)

proofs: components/actuator.cn \
 components/instrumentation_common.cn \
 components/instrumentation.cn \
 components/actuation_unit.cn \
 posix_main.cn

%.cn: %.c
	$(CN) $<

components/actuation_unit.cn: components/actuation_unit.c
	$(CN) $< --skip=actuation_logic_collect_trips
#send_actuation_command malloc
#read_actuation_command global variables and a scope issue, CN issue #353
#update_sensor_errors contains a 2-level and 3-level array with the same variables used as indices in both, CN issue #357
#update_sensors also CN issue #357
#clear_screen need to claim that stdin is a valid pointer while using `accesses`. Could just use take but it's a global
posix_main.cn: posix_main.c
	$(CN) $< --skip=main,start1,start0,update_sensor_errors,clear_screen,update_sensors,send_actuation_command,read_actuation_command
