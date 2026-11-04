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
val _ = show "loc_ok_word_addr_typed" data_to_word_gcProofTheory.loc_ok_word_addr;
val _ = show "word_gc_move_thm_typed" data_to_word_gcProofTheory.word_gc_move_thm;
val _ = show "word_gc_move_roots_thm_typed" data_to_word_gcProofTheory.word_gc_move_roots_thm;
val _ = show "word_gc_move_list_thm_typed" data_to_word_gcProofTheory.word_gc_move_list_thm;
val _ = show "word_payload_swap_typed" data_to_word_gcProofTheory.word_payload_swap;
val _ = show "word_gc_move_loop_thm_typed" data_to_word_gcProofTheory.word_gc_move_loop_thm;
val _ = show "word_full_gc_thm_typed" data_to_word_gcProofTheory.word_full_gc_thm;
val _ = show "full_gc_IMP_typed" data_to_word_gcProofTheory.full_gc_IMP;
val _ = show "word_gc_fun_lemma_Simple_typed" data_to_word_gcProofTheory.word_gc_fun_lemma_Simple;
val _ = show "word_gc_fun_lemma_typed" data_to_word_gcProofTheory.word_gc_fun_lemma;
val _ = show "do_partial_typed" data_to_word_gcProofTheory.do_partial_def;
val _ = show "make_gc_conf_typed" data_to_word_memoryProofTheory.make_gc_conf_def;
val _ = show "is_Ref_typed" data_to_word_gcProofTheory.is_Ref_def;
val _ = show "len_inv_typed" data_to_word_gcProofTheory.len_inv_def;
val _ = show "word_gen_gc_move_thm_typed" data_to_word_gcProofTheory.word_gen_gc_move_thm;
val _ = show "is_ref_header_alt_typed" data_to_word_gcProofTheory.is_ref_header_alt;
val _ = show "is_ref_header_thm_typed" data_to_word_gcProofTheory.is_ref_header_thm;
val _ = show "gc_move_with_NIL_typed" data_to_word_gcProofTheory.gc_move_with_NIL;
val _ = show "gc_move_with_NIL_LEMMA_typed" data_to_word_gcProofTheory.gc_move_with_NIL_LEMMA;
val _ = show "gc_move_list_with_NIL_typed" data_to_word_gcProofTheory.gc_move_list_with_NIL;
val _ = show "gc_move_list_with_NIL_LEMMA_typed" data_to_word_gcProofTheory.gc_move_list_with_NIL_LEMMA;
val _ = show "gen_gc_move_ok_typed" gen_gcTheory.gc_move_ok;
val _ = show "gen_gc_move_list_ok_typed" gen_gcTheory.gc_move_list_ok;
val _ = show "word_gen_gc_move_roots_thm_typed" data_to_word_gcProofTheory.word_gen_gc_move_roots_thm;
val _ = show "word_gen_gc_move_list_thm_typed" data_to_word_gcProofTheory.word_gen_gc_move_list_thm;
val _ = show "word_heap_parts_typed" data_to_word_gcProofTheory.word_heap_parts_def;
val _ = show "gc_move_const_typed" data_to_word_gcProofTheory.gc_move_const;
val _ = show "gc_move_list_const_typed" data_to_word_gcProofTheory.gc_move_list_const;
val _ = show "gc_move_data_const_typed" data_to_word_gcProofTheory.gc_move_data_const;
val _ = show "gc_move_refs_const_typed" data_to_word_gcProofTheory.gc_move_refs_const;
val _ = show "heap_length_gc_forward_ptr_typed" data_to_word_gcProofTheory.heap_length_gc_forward_ptr;
val _ = show "gen_move_len_inv_typed" data_to_word_gcProofTheory.gc_move_thm;
val _ = show "gen_move_list_len_inv_typed" data_to_word_gcProofTheory.gc_move_list_thm;
val _ = show "gc_shared_empty_state_typed" gc_sharedTheory.empty_state_def;
val _ = show "gc_shared_heap_segment_typed" gc_sharedTheory.heap_segment_def;
val _ = show "gen_gc_move_typed" gen_gcTheory.gc_move_def;
val _ = show "gen_gc_move_list_typed" gen_gcTheory.gc_move_list_def;
val _ = show "gen_gc_move_data_typed" gen_gcTheory.gc_move_data_def;
val _ = show "gen_gc_move_refs_typed" gen_gcTheory.gc_move_refs_def;
val _ = show "gen_gc_move_loop_typed" gen_gcTheory.gc_move_loop_def;
val _ = show "gen_gc_typed" gen_gcTheory.gen_gc_def;
val _ = show "partial_gc_move_typed" gen_gc_partialTheory.gc_move_def;
val _ = show "gen_gc_move_data_ok_typed" gen_gcTheory.gc_move_data_ok;
val _ = show "gen_gc_move_refs_ok_typed" gen_gcTheory.gc_move_refs_ok;
val _ = show "gen_gc_move_loop_ok_typed" gen_gcTheory.gc_move_loop_ok;
val _ = show "word_gen_gc_move_loop_thm_typed" data_to_word_gcProofTheory.word_gen_gc_move_loop_thm;
val _ = show "word_gen_gc_thm_typed" data_to_word_gcProofTheory.word_gen_gc_thm;
val _ = show "heap_drop_typed" gc_sharedTheory.heap_drop_def;
val _ = show "heap_take_typed" gc_sharedTheory.heap_take_def;
val _ = show "heap_split_heap_length_typed" gc_sharedTheory.heap_split_heap_length;
val _ = show "heap_segment_imp_typed" gc_sharedTheory.heap_segment_IMP;
val _ = show "heap_split_append_typed" data_to_word_gcProofTheory.heap_split_APPEND;
val _ = show "heap_split_append_sum_typed" data_to_word_gcProofTheory.heap_split_APPEND';
val _ = show "heap_drop_append_typed" data_to_word_gcProofTheory.heap_drop_APPEND;
val _ = show "heap_take_append_typed" data_to_word_gcProofTheory.heap_take_APPEND;
val _ = show "heap_drop_zero_typed" data_to_word_gcProofTheory.heap_drop_0;
val _ = show "gc_forward_ptr_append_typed" data_to_word_gcProofTheory.gc_forward_ptr_APPEND;
val _ = show "partial_gc_forward_ptr_heap_length_typed" gen_gc_partialTheory.gc_forward_ptr_heap_length;
val _ = show "gc_forward_ptr_heap_split_typed" data_to_word_gcProofTheory.gc_forward_ptr_heap_split;
val _ = show "partial_gc_move_heap_split_typed" data_to_word_gcProofTheory.partial_gc_move_heap_split;
val _ = show "partial_gc_move_list_heap_split_typed" data_to_word_gcProofTheory.partial_gc_move_list_heap_split;
val _ = show "partial_gc_move_heap_length_typed" gen_gc_partialTheory.gc_move_heap_length;
val _ = show "length_less_eq_sum_el_length_typed" data_to_word_gcProofTheory.LENGTH_LESS_EQ_SUM_el_length;
val _ = show "gen_gc_move_data_h2_typed" gen_gcTheory.gc_move_data_h2;
val _ = show "gen_gc_move_list_length_typed" gen_gcTheory.gc_move_list_length;
val _ = show "gen_gc_length_typed" gen_gcTheory.gen_gc_LENGTH;
val _ = show "muttag_header_typed" data_to_word_gcProofTheory.muttag_header_def;
val _ = show "is_mut_tag_word_payload_typed" data_to_word_gcProofTheory.isMutTag_word_payload_IMP;
val _ = show "word_gen_gc_move_refs_thm_typed" data_to_word_gcProofTheory.word_gen_gc_move_refs_thm;
val _ = show "word_gen_gc_move_data_thm_typed" data_to_word_gcProofTheory.word_gen_gc_move_data_thm;
val _ = show "word_list_IMP_limit_typed" data_to_word_gcProofTheory.word_list_IMP_limit;
val _ = show "word_el_eq_word_list_typed" data_to_word_gcProofTheory.word_el_eq_word_list;
val _ = show "word_heap_eq_word_list_strong_typed" data_to_word_gcProofTheory.word_heap_eq_word_list_strong;
val _ = show "word_heap_eq_word_list_typed" data_to_word_gcProofTheory.word_heap_eq_word_list;
val _ = show "word_heap_IMP_limit_typed" data_to_word_gcProofTheory.word_heap_IMP_limit;
val _ = show "partial_gc_move_list_typed" gen_gc_partialTheory.gc_move_list_def;
val _ = show "partial_gc_move_ref_list_typed" gen_gc_partialTheory.gc_move_ref_list_def;
val _ = show "partial_gc_move_data_typed" gen_gc_partialTheory.gc_move_data_def;
val _ = show "partial_gc_typed" gen_gc_partialTheory.partial_gc_def;
val _ = show "make_partial_conf_typed" gc_combinedTheory.make_partial_conf_def;
val _ = show "gc_combined_typed" gc_combinedTheory.gc_combined_def;
fun evalshow label term = (print label; print "="; print_term (rhs (concl (SIMP_RULE (srw_ss()) [] (EVAL term)))); print "\n");
val _ = evalshow "gen_gc_reference_move" ``
  let s = (empty_state:(num,num) gc_state) with <| heap := [DataElement [] 0 42]; n := 3 |> in
  let (p,t) = gen_gc$gc_move <| limit := 3; isRef := (\x. x = 42) |> s (Pointer 0 7) in
  (p,t.a,t.n,t.ok,t.r4,t.h2)``;
val _ = evalshow "gen_gc_data_move" ``
  let s = (empty_state:(num,num) gc_state) with <| heap := [DataElement [] 0 42]; n := 3 |> in
  let (p,t) = gen_gc$gc_move <| limit := 3; isRef := (\x. F) |> s (Pointer 0 7) in
  (p,t.a,t.n,t.ok,t.r4,t.h2)``;
val _ = evalshow "partial_gc_forward_ignores_bound_status" ``
  let s = (empty_state:(num,num) gc_state) with <| heap := [ForwardPointer 2 9 0]; n := 3; ok := F |> in
  let (p,t) = gen_gc_partial$gc_move <| limit := 3; isRef := (\x. F); gen_start := 0; refs_start := 3 |> s (Pointer 0 7) in
  (p,t.a,t.n,t.ok)``;
val _ = evalshow "combined_major_empty" ``
  gc_combined <| limit := 0; isRef := (\x:num. F) |> (Generational [0])
    (([]:num heap_address list),([]:(num,num) heap_element list),GenState 0 [0],0,F)``;
val _ = evalshow "combined_minor_empty" ``
  gc_combined <| limit := 0; isRef := (\x:num. F) |> (Generational [0])
    (([]:num heap_address list),([]:(num,num) heap_element list),GenState 0 [0],0,T)``;
val movePre = fst (dest_imp (concl data_to_word_gcProofTheory.word_gc_move_thm));
val moveSep = List.nth (strip_conj movePre, 2);
val moveStar = fst (dest_comb moveSep);
val moveFirst = snd (dest_comb (fst (dest_comb moveStar)));
val _ = (print "word_gc_move_first_star_argument="; Lib.with_flag (Globals.show_types,true) print_term moveFirst; print "\n");
val movePost = snd (dest_exists (snd (dest_imp (concl data_to_word_gcProofTheory.word_gc_move_thm))));
val movePostStar = fst (dest_comb (hd (strip_conj movePost)));
val movePostFirst = snd (dest_comb (fst (dest_comb movePostStar)));
val _ = (print "word_gc_move_result_first_star_argument="; Lib.with_flag (Globals.show_types,true) print_term movePostFirst; print "\n");
val _ = show "get_addr_and_1_not_0_typed" data_to_word_gcProofTheory.get_addr_and_1_not_0;
val _ = show "ptr_to_addr_get_addr_typed" data_to_word_gcProofTheory.ptr_to_addr_get_addr;
val _ = show "NOT_is_fwd_ptr_typed" data_to_word_gcProofTheory.NOT_is_fwd_ptr;
val _ = show "memcpy_thm_typed" data_to_word_gcProofTheory.memcpy_thm;
val _ = show "memcpy_def_typed" word_gcFunctionsTheory.memcpy_def;
val memcpyPre = fst (dest_imp (snd (strip_forall (concl data_to_word_gcProofTheory.memcpy_thm))));
val memcpySep = List.nth (strip_conj memcpyPre, 3);
val memcpyStar = fst (dest_comb memcpySep);
val memcpyFirst = snd (dest_comb (fst (dest_comb memcpyStar)));
val _ = (print "memcpy_first_star_argument="; Lib.with_flag (Globals.show_types,true) print_term memcpyFirst; print "\n");
