(* Typed source declarations for pan_to_crepProof (task 148). *)
load "preamble";
load "pan_to_crepProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble pan_to_crepProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="pan_to_crepProof",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by pan_to_crepProof")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of pan_to_crepProof")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "ctxt_fc_eids_eq_typed" "ctxt_fc_eids_eq";
val _ = emit "ctxt_fc_def_typed" "ctxt_fc_def";
val _ = emit "ctxt_fc_funcs_eq_typed" "ctxt_fc_funcs_eq";
val _ = emit "ctxt_fc_vmax_typed" "ctxt_fc_vmax";
val _ = emit "EL_load_globals_typed" "EL_load_globals";
val _ = emit "evaluate_replicate_const_typed" "evaluate_replicate_const";
val _ = emit "filter_not_mem_self_typed" "filter_not_mem_self";
val _ = emit "first_compile_to_crep_all_distinct_typed" "first_compile_to_crep_all_distinct";
val _ = emit "is_wf_shape_nil_length_flatten_typed" "is_wf_shape_nil_length_flatten";
val _ = emit "load_shape_el_rel_typed" "load_shape_el_rel";
val _ = emit "MAP_SOME_MEM_lemma_typed" "MAP_SOME_MEM_lemma";
val _ = emit "MAX_LIST_APPEND_typed" "MAX_LIST_APPEND";
val _ = emit "MAX_LIST_NOT_MEM_typed" "MAX_LIST_NOT_MEM";
val _ = emit "mem_comp_field_typed" "mem_comp_field";
val _ = emit "mem_comp_field_lem_typed" "mem_comp_field_lem";
val _ = emit "mod_eq_lt_eq_typed" "mod_eq_lt_eq";
val _ = emit "not_none_then_some_typed" "not_none_then_some";
val _ = emit "code_rel_def_typed" "code_rel_def";
val _ = emit "code_rel_empty_locals_typed" "code_rel_empty_locals";
val _ = emit "code_rel_imp_typed" "code_rel_imp";
val _ = emit "mk_ctxt_code_imp_code_rel_typed" "mk_ctxt_code_imp_code_rel";
val _ = emit "compile_exp_val_rel_typed" "compile_exp_val_rel";
val _ = emit "eval_map_comp_exp_flat_eq_typed" "eval_map_comp_exp_flat_eq";
val _ = emit "compile_prog_distinct_params_typed" "compile_prog_distinct_params";
val _ = emit "eval_distinct_lists_not_affect_typed" "eval_distinct_lists_not_affect";
val _ = emit "opt_mmap_eval_distinct_lists_not_affect_typed" "opt_mmap_eval_distinct_lists_not_affect";
val _ = emit "eval_nested_assign_distinct_eq_typed" "eval_nested_assign_distinct_eq";
val _ = emit "eval_nested_decs_seq_res_var_eq_typed" "eval_nested_decs_seq_res_var_eq";
val _ = emit "evaluate_nested_decs_load_globals_typed" "evaluate_nested_decs_load_globals";
val _ = emit "globals_lookup_def_typed" "globals_lookup_def";
val _ = emit "first_compile_prog_all_distinct_typed" "first_compile_prog_all_distinct";
val _ = emit "not_mem_context_assigned_mem_gt_typed" "not_mem_context_assigned_mem_gt";
val _ = emit "pc_compile_correct_typed" "pc_compile_correct";
val _ = emit "pan_primop_crep_primop_typed" "pan_primop_crep_primop";
val _ = emit "ctxt_max_el_leq_typed" "ctxt_max_el_leq";
val _ = emit "locals_rel_extend_new_var_typed" "locals_rel_extend_new_var";
val _ = emit "no_overlap_wrap_rt_some_all_distinct_typed" "no_overlap_wrap_rt_some_all_distinct";
val _ = emit "opt_mmap_eval_is_wf_shape_v_typed" "opt_mmap_eval_is_wf_shape_v";
val _ = emit "excp_rel_def_typed" "excp_rel_def";
val _ = emit "local_rel_gt_vmax_preserved_typed" "local_rel_gt_vmax_preserved";
val _ = emit "locals_rel_def_typed" "locals_rel_def";
val _ = emit "locals_rel_lookup_ctxt_typed" "locals_rel_lookup_ctxt";
val _ = emit "locals_rel_wf_shape_typed" "locals_rel_wf_shape";
val _ = emit "state_rel_def_typed" "state_rel_def";
val _ = emit "slc_def_typed" "slc_def";
val _ = emit "slc_tlc_rw_typed" "slc_tlc_rw";
val _ = emit "tlc_def_typed" "tlc_def";
val _ = emit "get_eids_imp_excp_rel_typed" "get_eids_imp_excp_rel";
val _ = emit "mk_ctxt_imp_locals_rel_typed" "mk_ctxt_imp_locals_rel";
val _ = emit "state_rel_imp_semantics_decls_to_crep_typed" "state_rel_imp_semantics_decls_to_crep";
val _ = emit "state_rel_imp_semantics_to_crep_typed" "state_rel_imp_semantics_to_crep";
val _ = emit "state_rel_imp_semantics_decls_typed" "state_rel_imp_semantics_decls";
val _ = emit "state_rel_imp_semantics_typed" "state_rel_imp_semantics";
val _ = emit "eval_map_var_cexp_present_ctxt_typed" "eval_map_var_cexp_present_ctxt";
val _ = emit "eval_var_cexp_present_ctxt_typed" "eval_var_cexp_present_ctxt";
val _ = emit "call_preserve_state_code_locals_rel_typed" "call_preserve_state_code_locals_rel";
