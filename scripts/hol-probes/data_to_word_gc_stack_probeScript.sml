load "preamble";
load "data_to_word_gcProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble;
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
val _ = show "alloc_size_typed" data_to_word_gcProofTheory.alloc_size_def;
val _ = show "alloc_size_check_typed" data_to_word_gcProofTheory.alloc_size_check;
val _ = show "alloc_size_LEQ_IMP_typed" data_to_word_gcProofTheory.alloc_size_LEQ_IMP;
val _ = show "gc_edge_typed" gc_sharedTheory.gc_edge_def;
val _ = show "reachable_addresses_typed" gc_sharedTheory.reachable_addresses_def;
val _ = show "heap_filter_aux_typed" gc_sharedTheory.heap_filter_aux_def;
val _ = show "heap_filter_typed" gc_sharedTheory.heap_filter_def;
val _ = show "heap_filter_EMPTY_typed" gc_sharedTheory.heap_filter_EMPTY;
val _ = show "all_reachable_from_roots_typed" data_to_word_memoryProofTheory.all_reachable_from_roots_def;
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
val _ = show "word_gen_gc_partial_move_thm_typed" data_to_word_gcProofTheory.word_gen_gc_partial_move_thm;
val _ = show "gen_gc_heap_lookup_append_typed" gen_gcTheory.heap_lookup_APPEND;
val _ = show "partial_move_ok_before_typed" data_to_word_gcProofTheory.gc_partial_move_ok_before;
val _ = show "partial_move_list_ok_before_typed" data_to_word_gcProofTheory.gc_partial_move_list_ok_before;
val _ = show "partial_move_with_nil_typed" data_to_word_gcProofTheory.gc_partial_move_with_NIL;
val _ = show "partial_move_list_with_nil_typed" data_to_word_gcProofTheory.gc_partial_move_list_with_NIL;
val _ = show "partial_move_list_with_nil_lemma_typed" data_to_word_gcProofTheory.gc_partial_move_list_with_NIL_LEMMA;
val _ = show "word_partial_move_roots_typed" data_to_word_gcProofTheory.word_gen_gc_partial_move_roots_thm;
val _ = show "word_partial_move_list_typed" data_to_word_gcProofTheory.word_gen_gc_partial_move_list_thm;
val _ = show "partial_move_data_ok_before_typed" data_to_word_gcProofTheory.gc_partial_move_data_ok_before;
val _ = show "partial_move_ref_list_ok_before_typed" data_to_word_gcProofTheory.gc_partial_move_ref_list_ok_before;
val _ = show "partial_move_ref_list_with_nil_typed" data_to_word_gcProofTheory.gc_partial_move_ref_list_with_NIL;
val _ = show "partial_move_ref_list_with_nil_lemma_typed" data_to_word_gcProofTheory.gc_partial_move_ref_list_with_NIL_LEMMA;
val _ = show "word_partial_move_ref_list_typed" data_to_word_gcProofTheory.word_gen_gc_partial_move_ref_list_thm;
val _ = show "partial_gc_move_ref_list_is_ref_typed" data_to_word_gcProofTheory.partial_gc_move_ref_list_isRef;
val _ = show "every_is_ref_is_ref_typed" data_to_word_gcProofTheory.EVERY_is_Ref_isRef;
val _ = show "ends_with_refs_typed" data_to_word_gcProofTheory.ends_with_refs_def;
val _ = show "word_gen_gc_partial_typed" data_to_word_gcProofTheory.word_gen_gc_partial_thm;
val _ = show "word_gen_gc_partial_full_typed" data_to_word_gcProofTheory.word_gen_gc_partial_full_thm;
val _ = show "partial_move_heap_lengths_typed" data_to_word_gcProofTheory.gc_partial_move_heap_lengths;
val _ = show "partial_move_list_heap_lengths_typed" data_to_word_gcProofTheory.gc_partial_move_list_heap_lengths;
val _ = show "partial_gc_move_list_heap_length_typed" gen_gc_partialTheory.gc_move_list_heap_length;
val _ = show "partial_len_inv_typed" data_to_word_gcProofTheory.partial_len_inv_def;
val _ = show "word_partial_move_data_typed" data_to_word_gcProofTheory.word_gen_gc_partial_move_data_thm;
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
val _ = show "partial_similar_ptr_typed" gen_gc_partialTheory.similar_ptr_def;
val _ = show "partial_similar_data_typed" gen_gc_partialTheory.similar_data_def;
val _ = show "partial_similar_data_lengths_typed" gen_gc_partialTheory.LIST_REL_similar_data_IMP;
val _ = show "make_partial_conf_typed" gc_combinedTheory.make_partial_conf_def;
val _ = show "gc_combined_typed" gc_combinedTheory.gc_combined_def;
val _ = show "addr_map_typed" gc_sharedTheory.ADDR_MAP_def;
val _ = show "gc_related_typed" gc_sharedTheory.gc_related_def;
val _ = show "heap_map_typed" gc_sharedTheory.heap_map_def;
val _ = show "heaps_similar_typed" gc_sharedTheory.heaps_similar_def;
val _ = show "heap_similar_data_imp_data_or_forward_typed" gc_sharedTheory.heap_similar_Data_IMP_DataOrForward;
val _ = show "is_some_forward_pointer_typed" gc_sharedTheory.isSomeForwardPointer_def;
val _ = show "is_some_data_or_forward_typed" gc_sharedTheory.isSomeDataOrForward_def;
val _ = show "is_some_data_or_forward_lemma_typed" gc_sharedTheory.isSomeDataOrForward_lemma;
val _ = show "heap_lookup_prefix_typed" gc_sharedTheory.heap_lookup_PREFIX;
val _ = show "heap_lookup_extend_typed" gc_sharedTheory.heap_lookup_EXTEND;
val _ = show "filter_lemma_typed" gc_sharedTheory.FILTER_LEMMA;
val _ = show "heaps_similar_refl_typed" gc_sharedTheory.heaps_similar_REFL;
val _ = show "heap_map_empty_typed" gc_sharedTheory.heap_map_EMPTY;
val _ = show "copying_gc_inv_typed" copying_gcTheory.gc_inv_def;
val _ = show "copying_heap_addresses_snoc_typed_replay"
  (prove (``!xs n x. heap_addresses n (xs ++ [x]) =
                     heap_addresses n xs UNION {heap_length xs + n}``,
          simp [gc_sharedTheory.heap_addresses_APPEND, gc_sharedTheory.heap_addresses_def,
                arithmeticTheory.ADD_COMM]));
val _ = show "heaps_similar_imp_heap_length_typed" gc_sharedTheory.heaps_similar_IMP_heap_length;
val _ = show "heap_similar_data_imp_typed" gc_sharedTheory.heap_similar_Data_IMP;
val _ = show "heaps_similar_lemma_typed" gc_sharedTheory.heaps_similar_lemma;
val _ = show "in_heap_map_imp_typed" gc_sharedTheory.IN_heap_map_IMP;
val _ = show "not_in_heap_map_typed" gc_sharedTheory.NOT_IN_heap_map;
val _ = show "heap_lookup_flookup_typed" gc_sharedTheory.heap_lookup_FLOOKUP;
val _ = show "heap_map1_typed" gc_sharedTheory.heap_map1_def;
val _ = show "heap_addresses_typed" gc_sharedTheory.heap_addresses_def;
val _ = show "heap_filter_aux_addresses_union_typed" gc_sharedTheory.heap_filter_aux_heap_addresses_UNION;
val _ = show "heap_length_heap_filter_typed" gc_sharedTheory.heap_length_heap_filter;
val _ = show "heap_length_heap_expand_typed" gc_sharedTheory.heap_length_heap_expand;
val _ = show "heap_length_heap_filter_eq_typed" gc_sharedTheory.heap_length_heap_filter_eq;
val _ = show "heap_length_heap_filter_insert_typed_replay" (prove (
  ``!heap. ~(e IN s) ==> (heap_length (heap_filter (e INSERT s) heap) =
    heap_length (heap_filter {e} heap) + heap_length (heap_filter s heap))``,
  fs [gc_sharedTheory.heap_filter_def]
  \\ qspec_tac (`0n`,`n:num`)
  \\ Induct_on `heap` \\ fs [gc_sharedTheory.heap_filter_aux_def, gc_sharedTheory.heap_length_def]
  \\ rpt strip_tac \\ fs [SUM_APPEND] \\ rw [] \\ fs []));
val _ = show "heap_filter_aux_append_typed" gc_sharedTheory.heap_filter_aux_APPEND;
val filter_shift = prove (
  ``!k n e heap. heap_filter_aux (k+n) {e+n} heap = heap_filter_aux k {e} heap``,
  Induct_on `heap` \\ fs [gc_sharedTheory.heap_filter_aux_def] \\ rw []
  \\ first_x_assum (qspecl_then [`k+el_length h`,`n`,`e`] mp_tac) \\ fs [])
  |> Q.SPEC `0` |> SIMP_RULE std_ss [];
val filter_zero = prove (
  ``!heap n. 0 < n ==> (heap_filter_aux n {0} heap = [])``,
  Induct \\ fs [gc_sharedTheory.heap_filter_aux_def]);
val _ = show "heap_lookup_imp_heap_filter_typed_replay" (prove (
  ``!heap e x. (heap_lookup e heap = SOME x) ==> (heap_filter {e} heap = [x])``,
  Induct \\ fs [gc_sharedTheory.heap_lookup_def] \\ rw []
  \\ fs [gc_sharedTheory.heap_filter_def, gc_sharedTheory.heap_filter_aux_def]
  \\ fs [NOT_LESS]
  THEN1 (match_mp_tac filter_zero \\ Cases_on `h` \\ EVAL_TAC \\ fs [])
  \\ fs [LESS_EQ_EXISTS] \\ rveq \\ fs [] \\ fs [filter_shift]));
val _ = show "heap_addresses_append_typed" gc_sharedTheory.heap_addresses_APPEND;
val _ = show "heap_addresses_less_heap_length_typed" gc_sharedTheory.heap_addresses_LESS_heap_length;
val _ = show "heap_addresses_less_typed" gc_sharedTheory.heap_addresses_LESS;
val _ = show "mem_imp_heap_lookup_typed" gc_sharedTheory.MEM_IMP_heap_lookup;
val _ = show "heap_lookup_imp_heap_addresses_typed" gen_gcTheory.heap_lookup_IMP_heap_addresses;
val _ = show "gc_related_append_heap_expand_typed" data_to_word_memoryProofTheory.gc_related_APPEND_heap_expand;
val _ = show "reachable_addresses_related_typed" data_to_word_memoryProofTheory.reachable_addresses_related;
val _ = show "imp_all_reachable_from_roots_typed" data_to_word_memoryProofTheory.IMP_all_reachable_from_roots;
val _ = show "addr_apply_typed" gc_sharedTheory.ADDR_APPLY_def;
val _ = show "addr_map_eq_typed" gc_sharedTheory.ADDR_MAP_EQ;
val _ = show "addr_map_length_typed" gc_sharedTheory.ADDR_MAP_LENGTH;
val _ = show "addr_map_append_typed" gc_sharedTheory.ADDR_MAP_APPEND;
val _ = show "mem_addr_map_typed" gc_sharedTheory.MEM_ADDR_MAP;
val _ = show "data_pointers_typed" data_to_word_memoryProofTheory.data_pointers_def;
val _ = show "lookup_len_typed" data_to_word_memoryProofTheory.lookup_len_def;
val _ = show "data_length_typed" data_to_word_memoryProofTheory.data_length_def;
val _ = show "data_pointers_heap_expand_typed" data_to_word_memoryProofTheory.data_pointers_heap_expand;
val _ = show "data_length_heap_expand_typed" data_to_word_memoryProofTheory.data_length_heap_expand;
val _ = show "data_length_cons_typed" data_to_word_memoryProofTheory.data_length_CONS;
val _ = show "data_length_append_typed" data_to_word_memoryProofTheory.data_length_APPEND;
val _ = show "data_length_append_heap_expand_typed" data_to_word_memoryProofTheory.data_length_APPEND_heap_expand;
val _ = show "data_length_heap_length_typed" data_to_word_memoryProofTheory.data_length_heap_length;
val _ = show "heap_lookup_expand_eq_some_typed" data_to_word_memoryProofTheory.heap_lookup_expand_eq_SOME;
val _ = show "is_some_data_element_heap_lookup_1256_typed_replay"
  (prove (``isSomeDataElement (heap_lookup a (heap ++ heap_expand n)) =
            isSomeDataElement (heap_lookup a heap)``,
          simp [gc_sharedTheory.isSomeDataElement_def, data_to_word_memoryProofTheory.heap_lookup_expand_eq_SOME]));
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
