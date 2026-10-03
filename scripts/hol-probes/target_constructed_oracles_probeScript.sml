load "preamble";
load "targetPropsTheory";
open HolKernel Parse preamble targetPropsTheory;
val _ = if null(hyp constructed_oracles_ffi_step) then
 (print "oracles_ffi_step_full_statement="; print_term(concl constructed_oracles_ffi_step); print "\n")
 else raise Fail "constructed_oracles_ffi_step hypotheses";
val _ = if null(hyp constructed_oracles_cc_step) then
 (print "oracles_cc_step_full_statement="; print_term(concl constructed_oracles_cc_step); print "\n")
 else raise Fail "constructed_oracles_cc_step hypotheses";
val _ = OS.Process.exit OS.Process.success;
