load "data_to_word_gcProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show label th =
  if null (hyp th) then
    (print label; print "="; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "stack_rel_typed" data_to_word_gcProofTheory.stack_rel_def;
val _ = show "the_global_typed" data_to_word_gcProofTheory.the_global_def;
val _ = show "contains_loc_typed" data_to_word_gcProofTheory.contains_loc_def;
val _ = show "limits_inv_typed" data_to_word_gcProofTheory.limits_inv_def;
val _ = show "join_env_typed" data_to_word_gcProofTheory.join_env_def;
val _ = show "flat_typed" data_to_word_gcProofTheory.flat_def;
val _ = show "flat_append_typed" data_to_word_gcProofTheory.flat_APPEND;
val _ = show "lookup_adjust_var_adjust_set_typed" data_to_word_gcProofTheory.lookup_adjust_var_adjust_set;
val _ = show "adjust_var_IN_adjust_set_typed" data_to_word_gcProofTheory.adjust_var_IN_adjust_set;
val _ = show "loc_merge_typed" data_to_word_gcProofTheory.loc_merge_def;
val _ = show "length_loc_merge_typed" data_to_word_gcProofTheory.LENGTH_loc_merge;
val _ = show "dec_stack_loc_merge_enc_stack_typed" data_to_word_gcProofTheory.dec_stack_loc_merge_enc_stack;
val _ = show "stack_rel_dec_stack_IMP_stack_rel_typed" data_to_word_gcProofTheory.stack_rel_dec_stack_IMP_stack_rel;
val _ = show "FILTER_enc_stack_lemma_typed" data_to_word_gcProofTheory.FILTER_enc_stack_lemma;
val _ = show "loc_ok_typed" data_to_word_gcProofTheory.loc_ok_def;
val _ = show "word_gc_move_roots_IMP_FILTER_typed" data_to_word_gcProofTheory.word_gc_move_roots_IMP_FILTER;
val _ = show "word_gen_gc_move_roots_IMP_FILTER_typed" data_to_word_gcProofTheory.word_gen_gc_move_roots_IMP_FILTER;
val _ = show "word_gen_gc_partial_move_roots_IMP_FILTER_typed" data_to_word_gcProofTheory.word_gen_gc_partial_move_roots_IMP_FILTER;
val _ = show "loc_merge_FILTER_isWord_typed" data_to_word_gcProofTheory.loc_merge_FILTER_isWord;
val _ = show "word_gc_fun_loc_merge_typed" data_to_word_gcProofTheory.word_gc_fun_loc_merge;
val _ = show "word_gc_fun_IMP_typed" data_to_word_gcProofTheory.word_gc_fun_IMP;
val _ = show "word_gc_fun_EL_lemma_typed" data_to_word_gcProofTheory.word_gc_fun_EL_lemma;
val _ = show "word_gc_fun_IMP_FILTER_typed" data_to_word_gcProofTheory.word_gc_fun_IMP_FILTER;
