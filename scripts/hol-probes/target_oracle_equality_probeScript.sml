load "preamble";
load "targetPropsTheory";
open HolKernel Parse preamble targetPropsTheory;
val _ = if null(hyp interference_count_EQ) then
 (print "count_eq_full_statement="; print_term(concl interference_count_EQ); print "\n")
 else raise Fail "interference_count_EQ hypotheses";
val _ = if null(hyp constructed_oracles_EQ) then
 (print "oracles_eq_full_statement="; print_term(concl constructed_oracles_EQ); print "\n")
 else raise Fail "constructed_oracles_EQ hypotheses";
val _ = OS.Process.exit OS.Process.success;
