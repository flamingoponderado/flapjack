load "preamble";
load "targetPropsTheory";
open HolKernel Parse preamble targetPropsTheory;
val _ = if null(hyp find_next_interference_const) then
 (print "search_const_full_statement="; print_term(concl find_next_interference_const); print "\n")
 else raise Fail "const hypotheses";
val _ = if null(hyp next_interference_const) then
 (print "next_const_full_statement="; print_term(concl next_interference_const); print "\n")
 else raise Fail "next const hypotheses";
val _ = OS.Process.exit OS.Process.success;
