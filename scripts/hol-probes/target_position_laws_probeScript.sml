load "preamble";
load "targetPropsTheory";
open HolKernel Parse preamble targetPropsTheory;
val _ = if null(hyp interference_count_tail) then
 (print "count_tail_full_statement="; print_term(concl interference_count_tail); print "\n")
 else raise Fail "count tail hypotheses";
val _ = if null(hyp interference_pos_head) then
 (print "pos_head_full_statement="; print_term(concl interference_pos_head); print "\n")
 else raise Fail "pos head hypotheses";
val _ = OS.Process.exit OS.Process.success;
