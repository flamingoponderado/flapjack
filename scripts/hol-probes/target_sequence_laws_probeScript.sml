load "preamble";
load "targetPropsTheory";
open HolKernel Parse preamble targetPropsTheory;
val _ = if null(hyp interference_app_seq_EQ) then
 (print "sequence_eq_full_statement="; print_term(concl interference_app_seq_EQ); print "\n")
 else raise Fail "sequence EQ hypotheses";
val _ = if null(hyp interference_app_seq_tail) then
 (print "sequence_tail_full_statement="; print_term(concl interference_app_seq_tail); print "\n")
 else raise Fail "sequence tail hypotheses";
val _ = if null(hyp interference_count_mono) then
 (print "count_mono_full_statement="; print_term(concl interference_count_mono); print "\n")
 else raise Fail "count mono hypotheses";
val _ = OS.Process.exit OS.Process.success;
