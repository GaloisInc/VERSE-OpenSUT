#CN_FLAGS=-I include --include=include/wars.h --magic-comment-char-dollar -I /Users/guso/.opam/default/lib/cerberus/runtime/libc/include/posix
CN_FLAGS=-I include -I ../../include --include=../../include/wars.h --magic-comment-char-dollar -DPLATFORM_HOST
#CN=cn verify --solver-type cvc5 $(CN_FLAGS)
CN=cn verify $(CN_FLAGS)

proofs: \
 components/instrumentation_common.cn \
 components/actuation_unit.cn \
 posix_main.cn \
 common.cn \
 core.cn

# some are verified but now hang or time out
#components/instrumentation.cn \
# all verified but hang or time out
 #sense_actuate.cn
 #components/actuator.cn

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
#actuation_logic_vote_trips_tgt times out
#output_actuation_signals_tgt times out
#actuation_unit_step_tgt times out
components/actuation_unit.cn: components/actuation_unit.c
	$(CN) $< --skip=actuation_logic_collect_trips,actuation_logic_vote_trips,output_actuation_signals,actuation_unit_step

components/instrumentation.cn: components/instrumentation.c
# CN #399
#	$(CN) $< --only=instrumentation_step_trip
# also CN #399
#	$(CN) $< --only=instrumentation_set_output_trips
#	$(CN) $< --skip=instrumentation_step_trip,instrumentation_step,instrumentation_set_output_trips
#	$(CN) $< --only=instrumentation_step
#	$(CN) $<

#send_actuation_command malloc
#read_actuation_command global variables and a scope issue, CN issue #353
#update_sensor_errors contains a 2-level and 3-level array with the same variables used as indices in both, CN issue #357
#update_sensors also CN issue #357
#clear_screen need to claim that stdin is a valid pointer while using `accesses`. Could just use take but it's a global
posix_main.cn: posix_main.c
#	$(CN) $< --skip=main,start1,start0,update_sensor_errors,clear_screen,update_sensors,send_actuation_command,read_actuation_command
	$(CN) $< --skip=main,read_actuation_command,send_actuation_command,update_display,update_sensors,clear_screen,update_sensor_errors,update_sensor_simulation

.PHONY: common.cn

#accesses common.c-local struct:
#  get_instrumentation_trip
#  get_instrumentation_value
#  get_instrumentation_mode
#  get_instrumentation_maintenance
#  reset_actuation_logic
#timeout/hang:
#  get_test_instrumentation
#  get_instrumentation_test_setpoints
#other:
#  set_output_actuation_logic
#  read_test_instrumentation_channel
#  read_instrumentation_trip_signals
common.cn:  common.c
	$(CN) $< --skip=get_instrumentation_trip,get_instrumentation_value,get_instrumentation_mode,get_instrumentation_maintenance,reset_actuation_logic,set_output_actuation_logic,read_test_instrumentation_channel,read_instrumentation_trip_signals,get_test_instrumentation,get_instrumentation_test_setpoints,get_test_device,get_test_actuation_unit

#update_ui_actuation needs to reason about c strings and that snprint, mostly the reference to the string literal though
#set_display_line needs to handle strings and use memset
#core_step and core_init have trouble with core_state_ok
core.cn: core.c
	$(CN) $< --skip=update_ui_actuation,set_display_line,core_step,core_init,update_ui,update_ui_actuation,update_ui_instr
	# undefined behavior in tests.inc.c currently
	#$(CN) -DENABLE_SELF_TEST $< --skip=update_ui_actuation,set_display_line,core_step,core_init
