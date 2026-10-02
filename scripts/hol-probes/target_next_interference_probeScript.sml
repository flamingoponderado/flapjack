load "preamble";
load "targetPropsTheory";
open HolKernel Parse preamble targetPropsTheory;
val _ = if null(hyp next_interference_intro) then
 (print "next_intro_full_statement="; print_term(concl next_interference_intro); print "\n")
 else raise Fail "intro hypotheses";
val _ = if null(hyp next_interference_shift) then
 (print "next_shift_full_statement="; print_term(concl next_interference_shift); print "\n")
 else raise Fail "shift hypotheses";
val _ = OS.Process.exit OS.Process.success;
