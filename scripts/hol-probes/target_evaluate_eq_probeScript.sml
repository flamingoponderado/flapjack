load "preamble";
load "targetPropsTheory";
open HolKernel Parse preamble targetPropsTheory;
val base = SPEC ``0:num`` evaluate_EQ_evaluate_lemma;
val _ = if null(hyp base) then
 (print "evaluate_eq_base_statement="; print_term(concl base); print "\n")
 else raise Fail "base hypotheses";
val _ = if null(hyp evaluate_EQ_evaluate_lemma) then
 (print "evaluate_eq_full_statement="; print_term(concl evaluate_EQ_evaluate_lemma); print "\n")
 else raise Fail "full theorem hypotheses";
val _ = OS.Process.exit OS.Process.success;
