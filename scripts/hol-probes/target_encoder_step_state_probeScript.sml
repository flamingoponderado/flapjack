load "preamble";
load "targetPropsTheory";
open HolKernel Parse preamble targetPropsTheory;
val _ = if null(hyp encoder_correct_asm_step_target_state_rel) then
 (print "encoder_step_state_full_statement="; print_term(concl encoder_correct_asm_step_target_state_rel); print "\n")
 else raise Fail "encoder step theorem hypotheses";
val _ = if null(hyp encoder_correct_RTC_asm_step_target_state_rel) then
 (print "encoder_rtc_state_full_statement="; print_term(concl encoder_correct_RTC_asm_step_target_state_rel); print "\n")
 else raise Fail "encoder RTC theorem hypotheses";
val _ = OS.Process.exit OS.Process.success;
