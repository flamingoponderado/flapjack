(* Typed source declarations for panProps (task 148). *)
load "preamble";
load "panPropsTheory";
open HolKernel Parse boolLib bossLib;
open preamble panPropsTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="panProps",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by panProps")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of panProps")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "OPT_MMAP_MEM_IMP_typed" "OPT_MMAP_MEM_IMP";
val _ = dt_label "semantics_run_res_typed" "semantics_run_res";
val _ = emit "decs_stcnames_only_functions2_typed" "decs_stcnames_only_functions2";
val _ = emit "decs_stcnames_only_functions_typed" "decs_stcnames_only_functions";
val _ = emit "every_exp_def_typed" "every_exp_def";
val _ = emit "exps_of_def_typed" "exps_of_def";
val _ = emit "length_flatten_eq_size_of_shape_typed" "length_flatten_eq_size_of_shape";
val _ = emit "functions_append_typed" "functions_append";
val _ = emit "functions_eq_FILTER_typed" "functions_eq_FILTER";
val _ = emit "functions_FILTER_typed" "functions_FILTER";
val _ = emit "is_wf_shape_v_nil_typed" "is_wf_shape_v_nil";
val _ = emit "is_wf_shape_v_def_typed" "is_wf_shape_v_def";
val _ = emit "is_wf_shape_v_drop_typed" "is_wf_shape_v_drop";
val _ = emit "is_wf_shape_of_v_typed" "is_wf_shape_of_v";
val _ = emit "localised_exp_real_def_typed" "localised_exp_real_def";
val _ = emit "localised_prog_def_typed" "localised_prog_def";
val _ = emit "mem_load_swap_memaddrs_typed" "mem_load_swap_memaddrs";
val _ = emit "mem_load_swap_memory_typed" "mem_load_swap_memory";
val _ = emit "mem_load_is_wf_shape_v_typed" "mem_load_is_wf_shape_v";
val _ = emit "mem_loads_some_shape_eq_typed" "mem_loads_some_shape_eq";
val _ = emit "mem_load_some_shape_eq_typed" "mem_load_some_shape_eq";
val _ = emit "nameless_exp_real_def_typed" "nameless_exp_real_def";
val _ = emit "pan_primop_is_wf_shape_v_typed" "pan_primop_is_wf_shape_v";
val _ = emit "shape_of_val_typed" "shape_of_val";
val _ = emit "size_of_sh_with_ctxt_eq_typed" "size_of_sh_with_ctxt_eq";
val _ = emit "eval_empty_locals_IMP_typed" "eval_empty_locals_IMP";
val _ = emit "eval_fresh_var_typed" "eval_fresh_var";
val _ = emit "eval_upd_clock_eq_typed" "eval_upd_clock_eq";
val _ = emit "eval_upd_code_eq_typed" "eval_upd_code_eq";
val _ = emit "eval_upd_eshapes_eq_typed" "eval_upd_eshapes_eq";
val _ = emit "eval_is_wf_shape_v_typed" "eval_is_wf_shape_v";
val _ = emit "eval_swap_memaddrs_typed" "eval_swap_memaddrs";
val _ = emit "eval_swap_memory_typed" "eval_swap_memory";
val _ = emit "evaluate_clock_sub_typed" "evaluate_clock_sub";
val _ = emit "evaluate_decls_append_typed" "evaluate_decls_append";
val _ = emit "evaluate_decl_commute_typed" "evaluate_decl_commute";
val _ = emit "evaluate_decls_eshapes_typed" "evaluate_decls_eshapes";
val _ = emit "evaluate_decls_exns_wf_typed" "evaluate_decls_exns_wf";
val _ = emit "evaluate_decls_functions_typed" "evaluate_decls_functions";
val _ = emit "evaluate_decls_memaddrs_mono_typed" "evaluate_decls_memaddrs_mono";
val _ = emit "evaluate_decls_names_typed" "evaluate_decls_names";
val _ = emit "evaluate_decls_only_exn_decls_typed" "evaluate_decls_only_exn_decls";
val _ = emit "evaluate_decls_only_functions_typed" "evaluate_decls_only_functions";
val _ = emit "evaluate_decls_only_funs_and_exn_decls_typed" "evaluate_decls_only_funs_and_exn_decls";
val _ = emit "evaluate_decls_swap_locals_typed" "evaluate_decls_swap_locals";
val _ = emit "evaluate_decls_swap_memaddrs_typed" "evaluate_decls_swap_memaddrs";
val _ = emit "evaluate_decls_swap_memory_typed" "evaluate_decls_swap_memory";
val _ = emit "evaluate_invariants_typed" "evaluate_invariants";
val _ = emit "exns_wf_evaluate_decls_typed" "exns_wf_evaluate_decls";
val _ = emit "io_events_eq_imp_ffi_eq_typed" "io_events_eq_imp_ffi_eq";
val _ = emit "lookup_code_wf_shape_invariant_step_typed" "lookup_code_wf_shape_invariant_step";
val _ = emit "opt_mmap_eval_upd_clock_eq_typed" "opt_mmap_eval_upd_clock_eq";
val _ = emit "OPT_MMAP_update_locals_not_vars_eval_eq_typed" "OPT_MMAP_update_locals_not_vars_eval_eq";
val _ = emit "update_locals_not_vars_eval_eq_eq_typed" "update_locals_not_vars_eval_eq_eq";
val _ = emit "update_locals_not_vars_eval_eq_typed" "update_locals_not_vars_eval_eq";
val _ = emit "update_locals_not_vars_eval_eq_NONE_typed" "update_locals_not_vars_eval_eq_NONE";
val _ = emit "evaluate_add_clock_eq_typed" "evaluate_add_clock_eq";
val _ = emit "evaluate_add_clock_io_events_mono_typed" "evaluate_add_clock_io_events_mono";
val _ = emit "evaluate_clock_sub1_typed" "evaluate_clock_sub1";
val _ = emit "evaluate_min_clock_typed" "evaluate_min_clock";
val _ = emit "evaluate_is_wf_shape_invariant_typed" "evaluate_is_wf_shape_invariant";
val _ = emit "list_rel_length_shape_of_flatten_typed" "list_rel_length_shape_of_flatten";
val _ = emit "localised_exp_simps_typed" "localised_exp_simps";
val _ = emit "nameless_exp_simps_typed" "nameless_exp_simps";
val _ = emit "pan_sem_is_wrapper_typed" "pan_sem_is_wrapper";
val _ = emit "FLOOKUP_pan_res_var_thm_typed" "FLOOKUP_pan_res_var_thm";
val _ = emit "flookup_res_var_diff_eq_org_typed" "flookup_res_var_diff_eq_org";
val _ = emit "flookup_res_var_some_eq_lookup_typed" "flookup_res_var_some_eq_lookup";
val _ = emit "length_with_shape_eq_shape_typed" "length_with_shape_eq_shape";
val _ = emit "all_distinct_with_shape_typed" "all_distinct_with_shape";
val _ = emit "el_mem_with_shape_typed" "el_mem_with_shape";
val _ = emit "mem_with_shape_length_typed" "mem_with_shape_length";
val _ = emit "with_shape_el_take_drop_eq_typed" "with_shape_el_take_drop_eq";
val _ = emit "all_distinct_with_shape_distinct_typed" "all_distinct_with_shape_distinct";
val _ = emit "all_distinct_disjoint_with_shape_typed" "all_distinct_disjoint_with_shape";
val _ = emit "all_distinct_mem_zip_disjoint_with_shape_typed" "all_distinct_mem_zip_disjoint_with_shape";
val _ = emit "el_el_with_shape_typed" "el_el_with_shape";
val _ = emit "list_rel_flatten_with_shape_length_typed" "list_rel_flatten_with_shape_length";
val _ = emit "list_rel_flatten_with_shape_flookup_typed" "list_rel_flatten_with_shape_flookup";
val _ = emit "semantics_wrapper_def_typed" "semantics_wrapper_def";
val _ = emit "semantics_wrapper_eq_typed" "semantics_wrapper_eq";
val _ = emit "evaluate_add_clock_or_timeout_typed" "evaluate_add_clock_or_timeout";
val _ = emit "evaluate_io_events_mono_typed" "evaluate_io_events_mono";
val _ = emit "evaluate_global_shape_invariant_typed" "evaluate_global_shape_invariant";
