#CN_FLAGS=-I include --include=include/wars.h --magic-comment-char-dollar -I /Users/guso/.opam/default/lib/cerberus/runtime/libc/include/posix
CN_FLAGS=-I include -I ../../include --include=../../include/wars.h --magic-comment-char-dollar -DPLATFORM_HOST -I $(OPAM_SWITCH_PREFIX)/lib/cerberus-lib/runtime/libc/include/posix
#CN=cn verify --solver-type cvc5 $(CN_FLAGS)
CN=cn verify $(CN_FLAGS)

proofs: \
 components/instrumentation_common.cn \
 components/actuation_unit.cn \
 posix_main.cn \
 common.cn \
 core.cn \
 sense_actuate.cn \
 components/instrumentation.cn \
 components/actuator.cn

# these have symbol naming issues but they should be processed eventually
# variants/instrumentation_handwritten_C.cn \
# variants/actuator_generated_C.cn \
# variants/saturation_generated_C.cn \
# variants/instrumentation_generated_C.cn \
# variants/actuation_unit_generated_C.cn \
# handwritten/C/instrumentation_impl.cn

# needed for a mode of core.c
# self_test_data/tests.inc.cn

# explicitly not included:
# bottom.cn is just assert(0) stubs
# generated/C/actuation_unit_impl.cn
# generated/C/instrumentation_impl.cn
# generated/C/saturation_impl.cn
# generated/C/actuator_impl.cn

%.cn: %.c
	$(CN) $<

#actuation_logic_collect_trips nested arrays, can be done
#actuation_logic_vote very slow
#actuation_unit_step very slow, might hang
components/actuation_unit.cn: components/actuation_unit.c
	$(CN) $< --skip=actuation_logic_collect_trips,actuation_unit_step,actuation_logic_vote

components/instrumentation.cn: components/instrumentation.c
	$(CN) $< --skip=instrumentation_step
#read_actuation_command global variables and a scope issue, CN issue #353
#send_actuation_command same as read
#update_sensor_errors not clear how to constrain values of error_sensor_mode
#update_sensors also CN issue #357
#main takes hours, very close to being specified though
posix_main.cn: posix_main.c
	$(CN) $< --skip=main,read_actuation_command,send_actuation_command,update_sensors,update_sensor_errors

.PHONY: common.cn

#not ok
#reset_actuation_logic very strange error, it should work
#read_test_instrumentation_channel similar error
#read_instrumentation_trip_signals multidim arrays might just be broken
common.cn:  common.c
	$(CN) $< --skip=reset_actuation_logic,read_test_instrumentation_channel,read_instrumentation_trip_signals

#update_ui_actuation needs to reason about c strings and that snprint, mostly the reference to the string literal though
#set_display_line needs to handle strings and use memset
#core_step and core_init have trouble with core_state_ok
core.cn: core.c
	$(CN) $< --skip=update_ui
	# undefined behavior in tests.inc.c currently
	#$(CN) -DENABLE_SELF_TEST $< --skip=update_ui_actuation,set_display_line,core_step,core_init
