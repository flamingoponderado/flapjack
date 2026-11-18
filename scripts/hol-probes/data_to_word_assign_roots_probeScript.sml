load "preamble";
load "data_to_word_gcProofTheory";
load "data_to_word_memoryProofTheory";
load "data_to_word_assignProofTheory";
load "data_to_word_bignumProofTheory";
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
val _ = emit "get_real_byte_offset_lemma_typed"
  data_to_word_assignProofTheory.get_real_byte_offset_lemma;
val _ = emit "reorder_lemma_typed" data_to_word_assignProofTheory.reorder_lemma;
val _ = emit "reorder_2_lemma_typed" data_to_word_assignProofTheory.reorder_2_lemma;
val _ = emit "word_ml_inv_num_typed" data_to_word_memoryProofTheory.word_ml_inv_num;
val _ = emit "word_ml_inv_neg_num_typed" data_to_word_memoryProofTheory.word_ml_inv_neg_num;
val _ = emit "word_ml_inv_zero_typed" data_to_word_memoryProofTheory.word_ml_inv_zero;
val _ = emit "memory_rel_Deref_prime_typed" data_to_word_memoryProofTheory.memory_rel_Deref';
val _ = emit "get_real_addr_lemma_typed" data_to_word_bignumProofTheory.get_real_addr_lemma;
val _ = emit "memcopy_def_typed" data_to_word_assignProofTheory.memcopy_def;
val _ = emit "MemCopy_thm_typed" data_to_word_assignProofTheory.MemCopy_thm;
val _ = emit "memory_rel_IMP_free_space_typed" data_to_word_assignProofTheory.memory_rel_IMP_free_space;
val _ = emit "store_list_def_typed" data_to_word_memoryProofTheory.store_list_def;
val _ = emit "IMP_store_list_SOME_typed" data_to_word_assignProofTheory.IMP_store_list_SOME;

val _ = emit "get_vars_cut_env_typed" data_to_word_assignProofTheory.get_vars_cut_env;
val _ = emit "get_vars_IMP_domain_typed" data_to_word_assignProofTheory.get_vars_IMP_domain;
val _ = emit "assign_ConsExtend_def_typed" data_to_wordTheory.assign_ConsExtend_def;
val _ = emit "assign_ConsExtend_expand_typed" data_to_word_assignProofTheory.assign_ConsExtend_expand;
