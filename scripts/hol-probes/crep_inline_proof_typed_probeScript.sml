(* Typed source declarations for crep_inlineProof (task 148). *)
load "preamble";
load "crep_inlineTheory";
load "crep_inlineProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble crep_inlineProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 thy name = DB.lookup {Thy=thy,Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 "crep_inlineProof" name of
    NONE => raise Fail (label ^ " is not exported by crep_inlineProof")
  | SOME (th,_) => show label th;

fun emit_ci label name =
  case fetch1 "crep_inline" name of
    NONE => raise Fail (label ^ " is not exported by crep_inline")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of crep_inlineProof")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "OPT_MMAP_ALL_EQ_typed" "OPT_MMAP_ALL_EQ";
val _ = emit "OPT_MMAP_SOME_ALL_typed" "OPT_MMAP_SOME_ALL";
val _ = emit "cont_res_def_typed" "cont_res_def";
val _ = emit "code_inl_rel_def_typed" "code_inl_rel_def";
val _ = emit "locals_ext_rel_def_typed" "locals_ext_rel_def";
val _ = emit "locals_rel_def_typed" "locals_rel_def";
val _ = emit "locals_rel_dec_clock_typed" "locals_rel_dec_clock";
val _ = emit "locals_strong_rel_def_typed" "locals_strong_rel_def";
val _ = emit "state_rel_code_def_typed" "state_rel_code_def";
val _ = emit "state_rel_def_typed" "state_rel_def";
val _ = emit "eval_code_inl_typed" "eval_code_inl";
val _ = emit "evaluate_locals_same_fdom_typed" "evaluate_locals_same_fdom";
val _ = emit "flookup_res_var_is_mem_zip_eq_typed" "flookup_res_var_is_mem_zip_eq";
val _ = emit "genlist_all_distinct_typed" "genlist_all_distinct";
val _ = emit "genlist_less_than_typed" "genlist_less_than";
val _ = emit "genlist_not_in_typed" "genlist_not_in";
val _ = emit "inline_prog_correct_typed" "inline_prog_correct";
val _ = emit "max_list_genlist_add_suc_val_typed" "max_list_genlist_add_suc_val";
val _ = emit "MORE_THEN_NOT_MAX_LIST_typed" "MORE_THEN_NOT_MAX_LIST";
val _ = emit "not_some_is_none_typed" "not_some_is_none";
val _ = emit "opt_mmap_eval_code_inl_typed" "opt_mmap_eval_code_inl";
val _ = emit "MEM_MAP2_IMP_typed" "MEM_MAP2_IMP";
val _ = emit "res_var_commutes_strong_typed" "res_var_commutes_strong";
val _ = emit "res_var_foldl_commutes_strong_typed" "res_var_foldl_commutes_strong";
val _ = emit "SUBMAP_IMP_DOMSUB_FUPDATE_typed" "SUBMAP_IMP_DOMSUB_FUPDATE";
val _ = emit "SUBMAP_IMP_DOMSUB_SUBMAP_typed" "SUBMAP_IMP_DOMSUB_SUBMAP";
val _ = emit "SUBMAP_IMP_FUPDATE_SUBMAP_typed" "SUBMAP_IMP_FUPDATE_SUBMAP";
val _ = emit "general_simulate_arg_load_correct_typed" "general_simulate_arg_load_correct";
val _ = emit "general_simulate_arg_load_preserve_locals_typed" "general_simulate_arg_load_preserve_locals";
val _ = emit "arg_load_correct_typed" "arg_load_correct";
val _ = emit "general_simulate_arg_load_strong_1_typed" "general_simulate_arg_load_strong_1";
val _ = emit "general_simulate_arg_load_strong_all_drule_typed" "general_simulate_arg_load_strong_all_drule";
val _ = emit "general_simulate_arg_load_strong_all_typed" "general_simulate_arg_load_strong_all";
val _ = emit "general_simulate_arg_load_strong_typed" "general_simulate_arg_load_strong";
val _ = emit "arg_load_stronger_typed" "arg_load_stronger";
val _ = emit "eval_dec_clock_eq_typed" "eval_dec_clock_eq";
val _ = emit "opt_mmap_eval_dec_clock_eq_typed" "opt_mmap_eval_dec_clock_eq";
val _ = emit "evaluate_state_locals_rel_typed" "evaluate_state_locals_rel";
val _ = emit "evaluate_state_locals_rel_strong_typed" "evaluate_state_locals_rel_strong";
val _ = emit "eval_state_locals_same_code_fdom_same_typed" "eval_state_locals_same_code_fdom_same";
val _ = emit "eval_optmmap_state_locals_rel_typed" "eval_optmmap_state_locals_rel";
val _ = emit "eval_original_extend_locals_rel_typed" "eval_original_extend_locals_rel";
val _ = emit "eval_state_locals_rel_typed" "eval_state_locals_rel";
val _ = emit "eval_original_extend_locals_typed" "eval_original_extend_locals";
val _ = emit "opt_mmap_flookup_some_then_same_fdom_typed" "opt_mmap_flookup_some_then_same_fdom";
val _ = emit "SUBMAP_IMP_FUPDATE_LIST_SUBMAP_typed" "SUBMAP_IMP_FUPDATE_LIST_SUBMAP";
val _ = emit "evaluate_nested_decs_locals_nested_res_var_drule_typed" "evaluate_nested_decs_locals_nested_res_var_drule";
val _ = emit "evaluate_nested_decs_locals_nested_res_var_typed" "evaluate_nested_decs_locals_nested_res_var";
val _ = emit "nested_decs_evaluate_typed" "nested_decs_evaluate";
val _ = emit "single_dec_evaluate_typed" "single_dec_evaluate";
val _ = emit "nested_decs_evaluate_sublocals_strong_typed" "nested_decs_evaluate_sublocals_strong";
val _ = emit "evaluate_nested_seq_assign_typed" "evaluate_nested_seq_assign";
val _ = emit "evaluate_nested_seq_assign_drule_typed" "evaluate_nested_seq_assign_drule";
val _ = emit "opt_mmap_flookup_not_mem_domsub_typed" "opt_mmap_flookup_not_mem_domsub";
val _ = emit "opt_mmap_some_imp_fupdate_exist_some_typed" "opt_mmap_some_imp_fupdate_exist_some";
val _ = emit "opt_mmap_some_imp_fupdate_list_exist_some_typed" "opt_mmap_some_imp_fupdate_list_exist_some";
val _ = emit "opt_mmap_update_locals_not_vars_eval_eq_typed" "opt_mmap_update_locals_not_vars_eval_eq";
val _ = emit "not_has_return_not_evaluate_return_typed" "not_has_return_not_evaluate_return";
val _ = emit "not_branch_ret_evaluate_return_unreach_elim_typed" "not_branch_ret_evaluate_return_unreach_elim";
val _ = emit "not_var_prog_flookup_eqn_typed" "not_var_prog_flookup_eqn";
val _ = emit "compile_inline_distinct_typed" "compile_inline_distinct";
val _ = emit "evaluate_call_same_result_state_typed" "evaluate_call_same_result_state";
val _ = emit "fst_map_3_f_typed" "fst_map_3_f";
val _ = emit "state_rel_imp_semantics_typed" "state_rel_imp_semantics";
val _ = emit "state_rel_imp_semantics_local_typed" "state_rel_imp_semantics_local";
val _ = emit "transform_branch_correct_typed" "transform_branch_correct";
val _ = emit "transform_eoc_correct_typed" "transform_eoc_correct";
val _ = emit "not_has_return_imp_not_branch_ret_typed" "not_has_return_imp_not_branch_ret";
val _ = emit "unreach_elim_arg_load_typed" "unreach_elim_arg_load";
val _ = emit "unreach_elim_arg_load_perm_typed" "unreach_elim_arg_load_perm";
val _ = emit "unreach_elim_converge_typed" "unreach_elim_converge";
val _ = emit "unreach_elim_fix_point_typed" "unreach_elim_fix_point";
val _ = emit "unreach_elim_nested_decs_typed" "unreach_elim_nested_decs";
val _ = emit "unreach_elim_correct_typed" "unreach_elim_correct";
val _ = emit "unreach_elim_not_none_evaluate_typed" "unreach_elim_not_none_evaluate";
val _ = emit "unreach_elim_preserve_has_return_typed" "unreach_elim_preserve_has_return";
val _ = emit "unreach_elim_preserve_not_branch_ret_typed" "unreach_elim_preserve_not_branch_ret";
val _ = emit "not_has_return_imp_unreach_elim_typed" "not_has_return_imp_unreach_elim";
val _ = emit "opt_mmap_update_list_locals_not_vars_eval_eq_typed" "opt_mmap_update_list_locals_not_vars_eval_eq";
val _ = emit "SUBMAP_DIFF_LIST_typed" "SUBMAP_DIFF_LIST";
val _ = emit "update_list_locals_not_vars_eval_eq_typed" "update_list_locals_not_vars_eval_eq";
val _ = emit "mem_var_prog_nested_seq_typed" "mem_var_prog_nested_seq";
val _ = emit "mem_var_prog_transform_branch_typed" "mem_var_prog_transform_branch";
val _ = emit "mem_var_prog_transform_eoc_typed" "mem_var_prog_transform_eoc";
val _ = emit "wrapped_transform_if_typed" "wrapped_transform_if";
val _ = emit "exps_of_nested_decs_typed" "exps_of_nested_decs";
val _ = emit "exps_of_nested_seq_assign_typed" "exps_of_nested_seq_assign";
val _ = emit "exps_of_arg_load_typed" "exps_of_arg_load";
val _ = emit "exps_of_unreach_elim_typed" "exps_of_unreach_elim";
val _ = emit "exps_of_transform_eoc_typed" "exps_of_transform_eoc";
val _ = emit "exps_of_transform_branch_typed" "exps_of_transform_branch";
val _ = emit "exps_of_inst_inline_typed" "exps_of_inst_inline";
val _ = emit "every_inst_crep_inline_typed" "every_inst_crep_inline";

val _ = emit_ci "compile_inl_prog_def_typed" "compile_inl_prog_def";
