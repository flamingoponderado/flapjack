load "preamble";
load "targetPropsTheory";
open HolKernel Parse preamble targetPropsTheory;
val _ = if null(hyp target_io_regs_callee_saved) then
 (print "io_callee_saved_full_statement="; print_term(concl target_io_regs_callee_saved); print "\n")
 else raise Fail "target_io_regs_callee_saved hypotheses";
val _ = if null(hyp target_cc_regs_callee_saved) then
 (print "cc_callee_saved_full_statement="; print_term(concl target_cc_regs_callee_saved); print "\n")
 else raise Fail "target_cc_regs_callee_saved hypotheses";
val _ = OS.Process.exit OS.Process.success;
