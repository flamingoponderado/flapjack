load "preamble";
load "targetPropsTheory";
open HolKernel Parse preamble targetPropsTheory;
val _ = if null(hyp find_next_interference_mono) then
  (print "search_mono_full_statement="; print_term(concl find_next_interference_mono); print "\n";
   print "search_mono_statement_type="; print_type(type_of(concl find_next_interference_mono)); print "\n")
  else raise Fail "mono hypotheses";
val _ = if null(hyp find_next_interference_unique) then
 (print "search_unique_full_statement="; print_term(concl find_next_interference_unique); print "\n")
 else raise Fail "unique hypotheses";
val _ = OS.Process.exit OS.Process.success;
