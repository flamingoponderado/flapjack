(* Typed source declarations for data_to_word_gcProof (task 148). *)
load "preamble";
load "data_to_word_gcProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble data_to_word_gcProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="data_to_word_gcProof",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by data_to_word_gcProof")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of data_to_word_gcProof")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "soundness_size_of_typed" "soundness_size_of";
val _ = emit "flat_PERM_extract_stack_typed" "flat_PERM_extract_stack";
val _ = emit "soundness_size_of_gen_typed" "soundness_size_of_gen";
val _ = emit "LENGTH_n2mw_LE_bignum_digits_typed" "LENGTH_n2mw_LE_bignum_digits";
val _ = emit "size_of_cons_typed" "size_of_cons";
val _ = emit "size_of_global_to_vs_typed" "size_of_global_to_vs";
val _ = emit "traverse_heap_reachable_set_mono_typed" "traverse_heap_reachable_set_mono";
val _ = emit "traverse_heap_reachable_aux_vars_gc_edge_typed" "traverse_heap_reachable_aux_vars_gc_edge";
val _ = emit "traverse_heap_reachable_RTC_gc_edge_typed" "traverse_heap_reachable_RTC_gc_edge";
val _ = emit "traverse_heap_reachable_typed" "traverse_heap_reachable";
val _ = emit "ALL_DISTINCT_data_pointers_typed" "ALL_DISTINCT_data_pointers";
val _ = emit "SUM_MAP_lookup_len_LESS_EQ_typed" "SUM_MAP_lookup_len_LESS_EQ";
val _ = emit "set_data_pointers_typed" "set_data_pointers";
val _ = emit "word_gc_fun_correct_typed" "word_gc_fun_correct";
val _ = emit "word_gen_gc_partial_full_thm_typed" "word_gen_gc_partial_full_thm";
val _ = emit "word_gen_gc_partial_thm_typed" "word_gen_gc_partial_thm";
val _ = emit "ends_with_refs_def_typed" "ends_with_refs_def";
val _ = emit "partial_gc_move_ref_list_isRef_typed" "partial_gc_move_ref_list_isRef";
val _ = emit "EVERY_is_Ref_isRef_typed" "EVERY_is_Ref_isRef";
val _ = emit "word_gen_gc_partial_move_ref_list_thm_typed" "word_gen_gc_partial_move_ref_list_thm";
val _ = emit "gc_partial_move_ref_list_ok_before_typed" "gc_partial_move_ref_list_ok_before";
val _ = emit "gc_partial_move_ref_list_with_NIL_typed" "gc_partial_move_ref_list_with_NIL";
val _ = emit "gc_partial_move_ref_list_with_NIL_LEMMA_typed" "gc_partial_move_ref_list_with_NIL_LEMMA";
val _ = emit "word_gen_gc_partial_move_data_thm_typed" "word_gen_gc_partial_move_data_thm";
val _ = emit "partial_len_inv_def_typed" "partial_len_inv_def";
val _ = emit "gc_partial_move_heap_lengths_typed" "gc_partial_move_heap_lengths";
val _ = emit "gc_partial_move_list_heap_lengths_typed" "gc_partial_move_list_heap_lengths";
val _ = emit "gc_partial_move_data_ok_before_typed" "gc_partial_move_data_ok_before";
val _ = emit "word_gen_gc_partial_move_list_thm_typed" "word_gen_gc_partial_move_list_thm";
val _ = emit "word_gen_gc_partial_move_roots_thm_typed" "word_gen_gc_partial_move_roots_thm";
val _ = emit "gc_partial_move_ok_before_typed" "gc_partial_move_ok_before";
val _ = emit "gc_partial_move_list_ok_before_typed" "gc_partial_move_list_ok_before";
val _ = emit "gc_partial_move_with_NIL_typed" "gc_partial_move_with_NIL";
val _ = emit "gc_partial_move_list_with_NIL_typed" "gc_partial_move_list_with_NIL";
val _ = emit "gc_partial_move_list_with_NIL_LEMMA_typed" "gc_partial_move_list_with_NIL_LEMMA";
val _ = emit "word_gen_gc_partial_move_thm_typed" "word_gen_gc_partial_move_thm";
val _ = emit "gc_forward_ptr_APPEND_typed" "gc_forward_ptr_APPEND";
val _ = emit "heap_split_APPEND_typed" "heap_split_APPEND";
val _ = emit "heap_drop_APPEND_typed" "heap_drop_APPEND";
val _ = emit "heap_take_APPEND_typed" "heap_take_APPEND";
val _ = emit "heap_drop_0_typed" "heap_drop_0";
val _ = emit "gc_forward_ptr_heap_split_typed" "gc_forward_ptr_heap_split";
val _ = emit "partial_gc_move_heap_split_typed" "partial_gc_move_heap_split";
val _ = emit "partial_gc_move_list_heap_split_typed" "partial_gc_move_list_heap_split";
val _ = emit "word_gen_gc_thm_typed" "word_gen_gc_thm";
val _ = emit "word_gen_gc_move_loop_thm_typed" "word_gen_gc_move_loop_thm";
val _ = emit "LENGTH_LESS_EQ_SUM_el_length_typed" "LENGTH_LESS_EQ_SUM_el_length";
val _ = emit "word_gen_gc_move_data_thm_typed" "word_gen_gc_move_data_thm";
val _ = emit "word_gen_gc_move_refs_thm_typed" "word_gen_gc_move_refs_thm";
val _ = emit "word_el_eq_word_list_typed" "word_el_eq_word_list";
val _ = emit "word_heap_eq_word_list_strong_typed" "word_heap_eq_word_list_strong";
val _ = emit "word_heap_eq_word_list_typed" "word_heap_eq_word_list";
val _ = emit "word_list_IMP_limit_typed" "word_list_IMP_limit";
val _ = emit "word_heap_IMP_limit_typed" "word_heap_IMP_limit";
val _ = emit "muttag_header_def_typed" "muttag_header_def";
val _ = emit "isMutTag_word_payload_IMP_typed" "isMutTag_word_payload_IMP";
val _ = emit "gc_move_data_const_typed" "gc_move_data_const";
val _ = emit "gc_move_refs_const_typed" "gc_move_refs_const";
val _ = emit "gc_move_const_typed" "gc_move_const";
val _ = emit "gc_move_list_const_typed" "gc_move_list_const";
val _ = emit "heap_length_gc_forward_ptr_typed" "heap_length_gc_forward_ptr";
val _ = emit "gc_move_thm_typed" "gc_move_thm";
val _ = emit "gc_move_list_thm_typed" "gc_move_list_thm";
val _ = emit "word_gen_gc_move_list_thm_typed" "word_gen_gc_move_list_thm";
val _ = emit "word_heap_parts_def_typed" "word_heap_parts_def";
val _ = emit "gc_move_with_NIL_typed" "gc_move_with_NIL";
val _ = emit "gc_move_list_with_NIL_typed" "gc_move_list_with_NIL";
val _ = emit "gc_move_list_with_NIL_LEMMA_typed" "gc_move_list_with_NIL_LEMMA";
val _ = emit "word_gen_gc_move_roots_thm_typed" "word_gen_gc_move_roots_thm";
val _ = emit "word_gen_gc_move_thm_typed" "word_gen_gc_move_thm";
val _ = emit "is_Ref_def_typed" "is_Ref_def";
val _ = emit "len_inv_def_typed" "len_inv_def";
val _ = emit "is_ref_header_alt_typed" "is_ref_header_alt";
val _ = emit "is_ref_header_thm_typed" "is_ref_header_thm";
val _ = emit "do_partial_def_typed" "do_partial_def";
val _ = emit "alloc_size_def_typed" "alloc_size_def";
val _ = emit "alloc_size_check_typed" "alloc_size_check";
val _ = emit "alloc_size_LEQ_IMP_typed" "alloc_size_LEQ_IMP";
val _ = emit "word_gc_fun_lemma_Simple_typed" "word_gc_fun_lemma_Simple";
val _ = emit "full_gc_IMP_typed" "full_gc_IMP";
val _ = emit "word_full_gc_thm_typed" "word_full_gc_thm";
val _ = emit "word_gc_move_loop_thm_typed" "word_gc_move_loop_thm";
val _ = emit "word_payload_swap_typed" "word_payload_swap";
val _ = emit "word_gc_move_list_thm_typed" "word_gc_move_list_thm";
val _ = emit "word_gc_move_roots_thm_typed" "word_gc_move_roots_thm";
val _ = emit "word_gc_move_thm_typed" "word_gc_move_thm";
val _ = emit "memcpy_thm_typed" "memcpy_thm";
val _ = emit "get_addr_and_1_not_0_typed" "get_addr_and_1_not_0";
val _ = emit "ptr_to_addr_get_addr_typed" "ptr_to_addr_get_addr";
val _ = emit "NOT_is_fwd_ptr_typed" "NOT_is_fwd_ptr";
val _ = emit "loc_ok_word_addr_typed" "loc_ok_word_addr";
val _ = emit "word_gc_fun_IMP_FILTER_typed" "word_gc_fun_IMP_FILTER";
val _ = emit "word_gc_fun_EL_lemma_typed" "word_gc_fun_EL_lemma";
val _ = emit "word_gc_fun_IMP_typed" "word_gc_fun_IMP";
val _ = emit "loc_merge_FILTER_isWord_typed" "loc_merge_FILTER_isWord";
val _ = emit "word_gc_fun_loc_merge_typed" "word_gc_fun_loc_merge";
val _ = emit "loc_ok_def_typed" "loc_ok_def";
val _ = emit "word_gc_move_roots_IMP_FILTER_typed" "word_gc_move_roots_IMP_FILTER";
val _ = emit "word_gen_gc_move_roots_IMP_FILTER_typed" "word_gen_gc_move_roots_IMP_FILTER";
val _ = emit "word_gen_gc_partial_move_roots_IMP_FILTER_typed" "word_gen_gc_partial_move_roots_IMP_FILTER";
val _ = emit "FILTER_enc_stack_lemma_typed" "FILTER_enc_stack_lemma";
val _ = emit "stack_rel_dec_stack_IMP_stack_rel_typed" "stack_rel_dec_stack_IMP_stack_rel";
val _ = emit "loc_merge_def_typed" "loc_merge_def";
val _ = emit "LENGTH_loc_merge_typed" "LENGTH_loc_merge";
val _ = emit "dec_stack_loc_merge_enc_stack_typed" "dec_stack_loc_merge_enc_stack";
val _ = emit "gc_fun_const_ok_word_gc_fun_typed" "gc_fun_const_ok_word_gc_fun";
val _ = emit "gc_fun_ok_word_gc_fun_typed" "gc_fun_ok_word_gc_fun";
val _ = emit "init_store_ok_def_typed" "init_store_ok_def";
val _ = emit "lsr_lsl_typed" "lsr_lsl";
val _ = emit "lookup_adjust_var_adjust_set_typed" "lookup_adjust_var_adjust_set";
val _ = emit "adjust_var_IN_adjust_set_typed" "adjust_var_IN_adjust_set";
val _ = emit "join_env_def_typed" "join_env_def";
val _ = emit "flat_def_typed" "flat_def";
val _ = emit "flat_APPEND_typed" "flat_APPEND";
val _ = emit "limits_inv_def_typed" "limits_inv_def";
val _ = emit "stack_rel_def_typed" "stack_rel_def";
val _ = emit "the_global_def_typed" "the_global_def";
val _ = emit "contains_loc_def_typed" "contains_loc_def";
