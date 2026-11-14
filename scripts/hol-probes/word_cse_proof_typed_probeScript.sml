(* Typed source declarations for word_cseProof (task 148). *)
load "preamble";
load "word_cseProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble word_cseProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="word_cseProof",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by word_cseProof")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of word_cseProof")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "arith_keys_eq_typed" "arith_keys_eq";
val _ = emit "canonicalRegs_correct_typed" "canonicalRegs_correct";
val _ = emit "canonicalRegs_correct_bis_typed" "canonicalRegs_correct_bis";
val _ = emit "comp_correct_typed" "comp_correct";
val _ = emit "word_common_subexp_elim_correct_typed" "word_common_subexp_elim_correct";
val _ = emit "every_inst_distinct_tar_reg_word_common_subexp_elim_typed" "every_inst_distinct_tar_reg_word_common_subexp_elim";
val _ = emit "full_inst_ok_less_word_common_subexp_elim_typed" "full_inst_ok_less_word_common_subexp_elim";
val _ = emit "pre_alloc_conventions_word_common_subexp_elim_typed" "pre_alloc_conventions_word_common_subexp_elim";
val _ = emit "word_cse_every_inst_distinct_tar_reg_typed" "word_cse_every_inst_distinct_tar_reg";
val _ = emit "word_cse_every_inst_two_reg_typed" "word_cse_every_inst_two_reg";
val _ = emit "word_cse_full_inst_ok_less_typed" "word_cse_full_inst_ok_less";
val _ = emit "word_cse_pre_alloc_conventions_typed" "word_cse_pre_alloc_conventions";
val _ = emit "canonicalArith_correct_typed" "canonicalArith_correct";
val _ = emit "data_inv_locals_typed" "data_inv_locals";
val _ = emit "data_inv_memory_typed" "data_inv_memory";
val _ = emit "data_inv_set_var_typed" "data_inv_set_var";
val _ = emit "data_inv_state_agree_typed" "data_inv_state_agree";
val _ = emit "data_inv_unset_var_typed" "data_inv_unset_var";
val _ = emit "not_seen_data_inv_alist_insert_typed" "not_seen_data_inv_alist_insert";
val _ = emit "wf_data_untracked_typed" "wf_data_untracked";
val _ = emit "data_inv_insert_to_canonical_typed" "data_inv_insert_to_canonical";
val _ = emit "data_inv_insert_to_latest_typed" "data_inv_insert_to_latest";
val _ = emit "data_inv_merge_l_typed" "data_inv_merge_l";
val _ = emit "data_inv_merge_r_typed" "data_inv_merge_r";
val _ = emit "data_inv_register_read_typed" "data_inv_register_read";
val _ = emit "data_inv_register_reads_typed" "data_inv_register_reads";
val _ = emit "data_inv_set_fp_var_typed" "data_inv_set_fp_var";
val _ = emit "data_inv_set_store_typed" "data_inv_set_store";
val _ = emit "data_inv_set_vars_typed" "data_inv_set_vars";
val _ = emit "empty_data_loads_wipe_typed" "empty_data_loads_wipe";
val _ = emit "evaluate_Move1_typed" "evaluate_Move1";
val _ = emit "lookup_empty_data_typed" "lookup_empty_data";
val _ = emit "evaluate_arith_set_var_typed" "evaluate_arith_set_var";
val _ = emit "add_to_data_Arith_correct_typed" "add_to_data_Arith_correct";
val _ = emit "add_to_data_LocValue_correct_typed" "add_to_data_LocValue_correct";
val _ = emit "add_to_data_OpCurrHeap_correct_typed" "add_to_data_OpCurrHeap_correct";
val _ = emit "add_to_data_aux_correct_typed" "add_to_data_aux_correct";
val _ = emit "add_to_data_const_correct_typed" "add_to_data_const_correct";
val _ = emit "add_to_load_aux_correct_typed" "add_to_load_aux_correct";
val _ = emit "add_to_load_correct_typed" "add_to_load_correct";
val _ = emit "in_names_set_def_typed" "in_names_set_def";
val _ = emit "insert_eq_typed" "insert_eq";
val _ = emit "bm_inter_eq_acc_thm_typed" "bm_inter_eq_acc_thm";
val _ = emit "lookup_bm_inter_eq_typed" "lookup_bm_inter_eq";
val _ = emit "invariant_bm_inter_eq_typed" "invariant_bm_inter_eq";
val _ = emit "arithOpToNum_eq_typed" "arithOpToNum_eq";
val _ = emit "memOpToNum_eq_typed" "memOpToNum_eq";
val _ = emit "shiftToNum_eq_typed" "shiftToNum_eq";
val _ = emit "wordToNum_unique_typed" "wordToNum_unique";
val _ = emit "firstRegOfArith_canonicalArith_typed" "firstRegOfArith_canonicalArith";
val _ = emit "invariant_listCmp_empty_typed" "invariant_listCmp_empty";
val _ = emit "lookup_insert_listCmp_typed" "lookup_insert_listCmp";
val _ = emit "lookup_listCmp_empty_typed" "lookup_listCmp_empty";
val _ = emit "lookup_register_read_typed" "lookup_register_read";
val _ = emit "lookup_register_reads_typed" "lookup_register_reads";
val _ = emit "register_read_simps_typed" "register_read_simps";
val _ = emit "register_reads_simps_typed" "register_reads_simps";
val _ = emit "antisym_listCmp_typed" "antisym_listCmp";
val _ = emit "good_cmp_listCmp_typed" "good_cmp_listCmp";
val _ = emit "listCmpEq_correct_typed" "listCmpEq_correct";
val _ = emit "TotOrd_listCmp_typed" "TotOrd_listCmp";
val _ = emit "transit_listCmp_typed" "transit_listCmp";
val _ = emit "evaluate_load_any_dest_typed" "evaluate_load_any_dest";
val _ = emit "evaluate_load_set_var_typed" "evaluate_load_set_var";
val _ = emit "MEM_FST_reduc_typed" "MEM_FST_reduc";
val _ = emit "canonicalMoveRegs_lemma_typed" "canonicalMoveRegs_lemma";
val _ = emit "data_inv_clock_typed" "data_inv_clock";
val _ = emit "get_set_vars_lemma_typed" "get_set_vars_lemma";
val _ = emit "lookup_map_insert0_typed" "lookup_map_insert0";
val _ = emit "data_inv_def_typed" "data_inv_def";
val _ = emit "data_inv_empty_typed" "data_inv_empty";
val _ = emit "sem_inv_def_typed" "sem_inv_def";
val _ = emit "wf_data_def_typed" "wf_data_def";
val _ = emit "wf_data_empty_typed" "wf_data_empty";
val _ = emit "wf_data_insert_to_canonical_typed" "wf_data_insert_to_canonical";
val _ = emit "wf_data_insert_to_latest_typed" "wf_data_insert_to_latest";
val _ = emit "wf_data_invalidate_typed" "wf_data_invalidate";
val _ = emit "wf_data_invalidate_regs_typed" "wf_data_invalidate_regs";
val _ = emit "wf_data_loads_wipe_typed" "wf_data_loads_wipe";
val _ = emit "wf_data_merge_typed" "wf_data_merge";
val _ = emit "wf_data_register_read_typed" "wf_data_register_read";
val _ = emit "wf_data_register_reads_typed" "wf_data_register_reads";
val _ = emit "wf_add_to_data_aux_typed" "wf_add_to_data_aux";
val _ = emit "wf_add_to_data_const_typed" "wf_add_to_data_const";
val _ = emit "wf_add_to_load_aux_typed" "wf_add_to_load_aux";
val _ = emit "wf_canonicalMoveRegs_typed" "wf_canonicalMoveRegs";
val _ = emit "word_cse_wf_data_typed" "word_cse_wf_data";
