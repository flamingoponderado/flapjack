load "preamble";
load "targetPropsTheory";
open HolKernel Parse preamble targetPropsTheory;
val _ = if null(hyp interference_count_lt) then
 (print "count_lt_full_statement="; print_term(concl interference_count_lt); print "\n")
 else raise Fail "count lt hypotheses";
val _ = if null(hyp interference_pos_unique) then
 (print "pos_unique_full_statement="; print_term(concl interference_pos_unique); print "\n")
 else raise Fail "pos unique hypotheses";
val _ = OS.Process.exit OS.Process.success;
