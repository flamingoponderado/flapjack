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
val _ = emit "fun2set_disjoint_union_typed" "fun2set_disjoint_union";
val _ = emit "UPDATE_LIST_def_typed" "UPDATE_LIST_def";
val _ = emit "APPLY_UPDATE_LIST_ALOOKUP_typed" "APPLY_UPDATE_LIST_ALOOKUP";
val _ = emit "MOD_SUB_LEMMA_typed" "MOD_SUB_LEMMA";
val _ = emit "DISJOINT_INTER_typed" "DISJOINT_INTER";
val _ = emit "IMP_MULT_DIV_LESS_typed" "IMP_MULT_DIV_LESS";
val _ = emit "DIV_LESS_DIV_typed" "DIV_LESS_DIV";
val _ = emit "WORD_LS_IMP_typed" "WORD_LS_IMP";
val _ = emit "SmartAppend_def_typed" "SmartAppend_def";
