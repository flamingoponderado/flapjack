(* Typed source declarations for misc (task 148). *)
load "preamble";
load "miscTheory";
open HolKernel Parse boolLib bossLib;
open preamble miscTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="misc",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by misc")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of misc")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "subspt_domain_SUBSET_typed" "subspt_domain_SUBSET";
val _ = emit "DISJOINT_IMAGE_SUC_typed" "DISJOINT_IMAGE_SUC";
val _ = emit "IMAGE_SUC_SUBSET_UNION_typed" "IMAGE_SUC_SUBSET_UNION";
val _ = emit "toAList_domain_typed" "toAList_domain";
val _ = emit "make_even_def_typed" "make_even_def";
val _ = emit "EVEN_make_even_typed" "EVEN_make_even";
val _ = emit "opt_bind_def_typed" "opt_bind_def";
val _ = emit "enumerate_def_typed" "enumerate_def";
val _ = emit "lookup_vars_def_typed" "lookup_vars_def";
val _ = emit "anub_def_typed" "anub_def";
val _ = emit "anub_all_distinct_keys_typed" "anub_all_distinct_keys";
val _ = dt_label "app_list_typed" "app_list";
val _ = emit "append_def_typed" "append_def";
val _ = emit "append_thm_typed" "append_thm";
val _ = emit "append_aux_def_typed" "append_aux_def";
val _ = emit "append_aux_thm_typed" "append_aux_thm";
val _ = emit "asm_write_bytearray_def_typed" "asm_write_bytearray_def";
val _ = emit "bytes_in_mem_def_typed" "bytes_in_mem_def";
val _ = emit "bytes_in_mem_IMP_typed" "bytes_in_mem_IMP";
val _ = emit "bytes_in_memory_def_typed" "bytes_in_memory_def";
val _ = emit "bytes_in_memory_APPEND_typed" "bytes_in_memory_APPEND";
val _ = emit "bytes_in_memory_change_mem_typed" "bytes_in_memory_change_mem";
val _ = emit "bytes_in_memory_in_domain_typed" "bytes_in_memory_in_domain";
val _ = emit "find_index_def_typed" "find_index_def";
val _ = emit "find_index_APPEND_typed" "find_index_APPEND";
val _ = emit "find_index_LESS_LENGTH_typed" "find_index_LESS_LENGTH";
val _ = emit "find_index_ALL_DISTINCT_EL_eq_typed" "find_index_ALL_DISTINCT_EL_eq";
val _ = emit "find_index_MEM_typed" "find_index_MEM";
val _ = emit "find_index_shift_typed" "find_index_shift";
val _ = emit "find_index_shift_0_typed" "find_index_shift_0";
val _ = emit "find_index_is_MEM_typed" "find_index_is_MEM";
val _ = emit "FLAT_REPLICATE_NIL_typed" "FLAT_REPLICATE_NIL";
val _ = emit "FOLDR_MAX_0_MAX_LIST_typed" "FOLDR_MAX_0_MAX_LIST";
val _ = emit "get_byte_set_byte_diff_typed" "get_byte_set_byte_diff";
val _ = emit "good_dimindex_get_byte_set_byte_typed" "good_dimindex_get_byte_set_byte";
val _ = emit "good_dimindex_def_typed" "good_dimindex_def";
val _ = emit "LLOOKUP_def_typed" "LLOOKUP_def";
val _ = emit "LLOOKUP_DROP_typed" "LLOOKUP_DROP";
val _ = emit "LLOOKUP_LUPDATE_typed" "LLOOKUP_LUPDATE";
val _ = emit "LLOOKUP_TAKE_IMP_typed" "LLOOKUP_TAKE_IMP";
val _ = emit "list_subset_def_typed" "list_subset_def";
val _ = emit "lookup_any_def_typed" "lookup_any_def";
val _ = emit "max3_def_typed" "max3_def";
val _ = emit "the_def_typed" "the_def";
val _ = emit "IMP_OPT_MMAP_EQ_typed" "IMP_OPT_MMAP_EQ";
val _ = emit "OPT_MMAP_CONG_typed" "OPT_MMAP_CONG";
val _ = emit "PERM_PART_typed" "PERM_PART";
val _ = emit "PERM_PARTITION_typed" "PERM_PARTITION";
val _ = emit "shift_seq_def_typed" "shift_seq_def";
val _ = emit "fromList2_def_typed" "fromList2_def";
val _ = emit "alist_insert_REVERSE_typed" "alist_insert_REVERSE";
val _ = emit "domain_fromList2_typed" "domain_fromList2";
val _ = emit "EVEN_fromList2_typed" "EVEN_fromList2";
val _ = emit "TAKE_FLAT_REPLICATE_LEQ_typed" "TAKE_FLAT_REPLICATE_LEQ";
val _ = emit "UNCURRY_eq_pair_typed" "UNCURRY_eq_pair";
val _ = emit "word_list_def_typed" "word_list_def";
val _ = emit "word_list_exists_def_typed" "word_list_exists_def";
val _ = emit "read_bytearray_def_typed" "read_bytearray_def";
val _ = emit "read_bytearray_LENGTH_typed" "read_bytearray_LENGTH";
val _ = emit "fun2set_disjoint_union_typed" "fun2set_disjoint_union";
val _ = emit "UPDATE_LIST_def_typed" "UPDATE_LIST_def";
val _ = emit "APPLY_UPDATE_LIST_ALOOKUP_typed" "APPLY_UPDATE_LIST_ALOOKUP";
val _ = emit "MOD_SUB_LEMMA_typed" "MOD_SUB_LEMMA";
val _ = emit "DISJOINT_INTER_typed" "DISJOINT_INTER";
val _ = emit "IMP_MULT_DIV_LESS_typed" "IMP_MULT_DIV_LESS";
val _ = emit "DIV_LESS_DIV_typed" "DIV_LESS_DIV";
val _ = emit "WORD_LS_IMP_typed" "WORD_LS_IMP";
val _ = emit "SmartAppend_def_typed" "SmartAppend_def";

(* Task 273: elementary tuple, num, list and set facts. *)
val _ = emit "FST_pair_typed" "FST_pair";
val _ = emit "SND_pair_typed" "SND_pair";
val _ = emit "FST_triple_typed" "FST_triple";
val _ = emit "SND_triple_typed" "SND_triple";
val _ = emit "LESS_1_typed" "LESS_1";
val _ = emit "MEM_REPLICATE_EQ_typed" "MEM_REPLICATE_EQ";
val _ = emit "LENGTH_TAKE_EQ_MIN_typed" "LENGTH_TAKE_EQ_MIN";
val _ = emit "w2n_lt_256_typed" "w2n_lt_256";
val _ = emit "IMP_IMP_typed" "IMP_IMP";
val _ = emit "SUBSET_IMP_typed" "SUBSET_IMP";
val _ = emit "DROP_NIL_typed" "DROP_NIL";
val _ = emit "times_add_o_typed" "times_add_o";
val _ = emit "FST_5tup_typed" "FST_5tup";
val _ = emit "SND_FST_pair_typed" "SND_FST_pair";
val _ = emit "plus_compose_typed" "plus_compose";
val _ = emit "option_case_NONE_F_typed" "option_case_NONE_F";
val _ = emit "MAP_FST_I_PAIR_MAP_typed" "MAP_FST_I_PAIR_MAP";
val _ = emit "FLAT_MAP_SING_typed" "FLAT_MAP_SING";
val _ = emit "FLAT_MAP_NIL_typed" "FLAT_MAP_NIL";
val _ = emit "ZIP_MAP_FST_SND_EQ_typed" "ZIP_MAP_FST_SND_EQ";
val _ = emit "MAP_EQ_ID_typed" "MAP_EQ_ID";
val _ = emit "SUM_REPLICATE_typed" "SUM_REPLICATE";
val _ = emit "SUM_MAP_LENGTH_REPLICATE_typed" "SUM_MAP_LENGTH_REPLICATE";
val _ = emit "EL_CONS_IF_typed" "EL_CONS_IF";
val _ = emit "EVERY_LAST_typed" "EVERY_LAST";
val _ = emit "revdroprev_typed" "revdroprev";
val _ = emit "o_PAIR_MAP_typed" "o_PAIR_MAP";
val _ = emit "EVERY_FST_SND_typed" "EVERY_FST_SND";
val _ = emit "EVERY_ZIP_typed" "EVERY_ZIP";
val _ = emit "EXISTS_ZIP_typed" "EXISTS_ZIP";
val _ = emit "TWOxDIV2_typed" "TWOxDIV2";
val _ = emit "DROP_EMPTY_typed" "DROP_EMPTY";
val _ = emit "DROP_IMP_LESS_LENGTH_typed" "DROP_IMP_LESS_LENGTH";
val _ = emit "MULT_DIV_MULT_LEMMA_typed" "MULT_DIV_MULT_LEMMA";
val _ = emit "ADD_MOD_EQ_LEMMA_typed" "ADD_MOD_EQ_LEMMA";
val _ = emit "SUM_MOD_typed" "SUM_MOD";
val _ = emit "LENGTH_enumerate_typed" "LENGTH_enumerate";
val _ = emit "MEM_enumerate_IMP_typed" "MEM_enumerate_IMP";
val _ = emit "DROP_EQ_CONS_IMP_DROP_SUC_typed" "DROP_EQ_CONS_IMP_DROP_SUC";
val _ = emit "LUPDATE_APPEND_typed" "LUPDATE_APPEND";
val _ = emit "DROP_LUPDATE_typed" "DROP_LUPDATE";
val _ = emit "ALOOKUP_SNOC_typed" "ALOOKUP_SNOC";
val _ = emit "ALOOKUP_ZIP_FAIL_typed" "ALOOKUP_ZIP_FAIL";
val _ = emit "map_fst_typed" "map_fst";
val _ = emit "map_some_eq_typed" "map_some_eq";
val _ = emit "MAP_EQ_MAP_IMP_typed" "MAP_EQ_MAP_IMP";
val _ = emit "OPTION_MAP_INJ_typed" "OPTION_MAP_INJ";
val _ = emit "the_OPTION_MAP_typed" "the_OPTION_MAP";
val _ = emit "MEM_REPLICATE_IMP_typed" "MEM_REPLICATE_IMP";
val _ = emit "MAP_K_REPLICATE_typed" "MAP_K_REPLICATE";
val _ = emit "SUM_MAP_K_typed" "SUM_MAP_K";
val _ = emit "OPTION_MAP_I_typed" "OPTION_MAP_I";
val _ = emit "TL_DROP_SUC_typed" "TL_DROP_SUC";
val _ = emit "ALL_DISTINCT_FLAT_EVERY_typed" "ALL_DISTINCT_FLAT_EVERY";
val _ = emit "OPT_MMAP_SOME_typed" "OPT_MMAP_SOME";
val _ = emit "insert_atI_def_typed" "insert_atI_def";
val _ = emit "LENGTH_insert_atI_typed" "LENGTH_insert_atI";
val _ = emit "OPT_MMAP_MAP_o_typed" "OPT_MMAP_MAP_o";
val _ = emit "list_inter_def_typed" "list_inter_def";
val _ = emit "list_set_eq_def_typed" "list_set_eq_def";
val _ = emit "any_el_def_typed" "any_el_def";
val _ = emit "option_fold_def_typed" "option_fold_def";
val _ = emit "steps_rel_def_typed" "steps_rel_def";
val _ = emit "DROP_IMP_EL_typed" "DROP_IMP_EL";
val _ = emit "HD_LUPDATE_typed" "HD_LUPDATE";
val _ = emit "zlookup_def_typed" "zlookup_def";
val _ = emit "tlookup_def_typed" "tlookup_def";
val _ = emit "steps_def_typed" "steps_def";
val _ = emit "LAST_MAP_SND_steps_FOLDL_typed" "LAST_MAP_SND_steps_FOLDL";
val _ = emit "LLOOKUP_EQ_EL_typed" "LLOOKUP_EQ_EL";
val _ = emit "LLOOKUP_THM_typed" "LLOOKUP_THM";
val _ = emit "IN_option_rwt2_typed" "IN_option_rwt2";
