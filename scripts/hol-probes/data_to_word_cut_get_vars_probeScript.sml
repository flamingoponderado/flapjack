load "preamble";
load "data_to_word_assignProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = show_types := true;
val lemma = data_to_word_assignProofTheory.cut_env_get_vars_get_vars;
val _ = if null (hyp lemma) then () else raise Fail "unexpected hypotheses";
val _ = (print "cut_env_get_vars_get_vars_typed="; print_term (concl lemma); print "\n");
