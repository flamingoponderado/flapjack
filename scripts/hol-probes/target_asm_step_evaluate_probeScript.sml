load "preamble";
load "targetPropsTheory";
open HolKernel Parse preamble targetPropsTheory;
val _ = if null(hyp asm_step_IMP_evaluate_step_find_next) then
 (print "asm_step_evaluate_full_statement="; print_term(concl asm_step_IMP_evaluate_step_find_next); print "\n")
 else raise Fail "step theorem hypotheses";
val _ = if null(hyp asm_step_IMP_evaluate_step) then
 (print "asm_step_evaluate_only_full_statement="; print_term(concl asm_step_IMP_evaluate_step); print "\n")
 else raise Fail "evaluator-only step theorem hypotheses";
val _ = OS.Process.exit OS.Process.success;
