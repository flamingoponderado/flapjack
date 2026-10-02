load "preamble";
load "targetPropsTheory";
open HolKernel Parse preamble targetPropsTheory;
val _ = if null(hyp interference_pos_tail_hit) then
 (print "pos_tail_hit_full_statement="; print_term(concl interference_pos_tail_hit); print "\n")
 else raise Fail "interference_pos_tail_hit hypotheses";
val _ = if null(hyp interference_pos_tail_miss) then
 (print "pos_tail_miss_full_statement="; print_term(concl interference_pos_tail_miss); print "\n")
 else raise Fail "interference_pos_tail_miss hypotheses";
val _ = OS.Process.exit OS.Process.success;
