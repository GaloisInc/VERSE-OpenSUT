#CN_FLAGS=-I include --include=include/wars.h --magic-comment-char-dollar -I /Users/guso/.opam/default/lib/cerberus/runtime/libc/include/posix
CN_FLAGS=-I include --include=include/wars.h --magic-comment-char-dollar
CN=cn verify $(CN_FLAGS)

proofs: components/actuator.cn \
 components/instrumentation_common.cn \
 components/instrumentation.cn \
 components/actuation_unit.cn \
 posix_main.cn \
 common.cn \
 core.cn \
 generated/C/actuation_unit_impl.cn \
 generated/C/instrumentation_impl.cn \
 generated/C/saturation_impl.cn \
 generated/C/actuator_impl.cn \
 sense_actuate.cn \
 self_test_data/tests.inc.cn \
 variants/instrumentation_handwritten_C.cn \
 variants/actuator_generated_C.cn \
 variants/saturation_generated_C.cn \
 variants/instrumentation_generated_C.cn \
 variants/actuation_unit_generated_C.cn \
 handwritten/C/instrumentation_impl.cn

# explicitly not included:
# bottom.cn is just assert(0) stubs

%.cn: %.c
	$(CN) $<

components/actuation_unit.cn: components/actuation_unit.c
	$(CN) $< #--skip=actuation_logic_collect_trips

components/instrumentation.cn: components/instrumentation.c
# CN #399
#	$(CN) $< --only=instrumentation_step_trip
# also CN #399
#	$(CN) $< --only=instrumentation_set_output_trips
	$(CN) $< --skip=instrumentation_step_trip,instrumentation_step,instrumentation_set_output_trips
	$(CN) $< --only=instrumentation_step

#send_actuation_command malloc
#read_actuation_command global variables and a scope issue, CN issue #353
#update_sensor_errors contains a 2-level and 3-level array with the same variables used as indices in both, CN issue #357
#update_sensors also CN issue #357
#clear_screen need to claim that stdin is a valid pointer while using `accesses`. Could just use take but it's a global
posix_main.cn: posix_main.c
	$(CN) $< --skip=main,start1,start0,update_sensor_errors,clear_screen,update_sensors,send_actuation_command,read_actuation_command
common.cn: common.c
	$(CN) $< --skip=get_test_actuation_unit,read_test_instrumentation_channel,get_instrumentation_test_setpoints,send_instrumentation_command,read_instrumentation_command,set_output_actuation_logic,reset_actuation_logic,read_instrumentation_trip_signals,get_actuation_state,get_instrumentation_maintenance,get_instrumentation_mode,get_instrumentation_trip,get_instrumentation_value,get_instrumentation_value

#update_ui_actuation needs to reason about c strings and that snprint, mostly the reference to the string literal though
core.cn: core.c
	$(CN) $< --skip=update_ui_actuation
