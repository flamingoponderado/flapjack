load "preamble";
load "data_to_word_gcProofTheory";
load "data_to_word_assignProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = show_types := true;
fun emit label th =
  if null (hyp th) then (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has unexpected hypotheses");
val _ = emit "word_ml_inv_get_vars_IMP_lemma_typed"
  data_to_word_gcProofTheory.word_ml_inv_get_vars_IMP_lemma;
val _ = emit "memory_rel_lookup_var_IMP_typed"
  data_to_word_assignProofTheory.memory_rel_lookup_var_IMP;
val _ = emit "get_real_offset_lemma_typed"
  data_to_word_assignProofTheory.get_real_offset_lemma;
