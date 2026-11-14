(* Typed source declarations for crepProps (task 148). *)
load "preamble";
load "crepPropsTheory";
open HolKernel Parse boolLib bossLib;
open preamble crepPropsTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="crepProps",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by crepProps")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of crepProps")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "assigned_free_vars_IMP_assigned_vars_typed" "assigned_free_vars_IMP_assigned_vars";
val _ = emit "assigned_free_vars_nested_decs_append_typed" "assigned_free_vars_nested_decs_append";
val _ = emit "nested_seq_assigned_free_vars_eq_typed" "nested_seq_assigned_free_vars_eq";
val _ = emit "assigned_free_vars_store_globals_empty_typed" "assigned_free_vars_store_globals_empty";
val _ = emit "assigned_free_vars_seq_store_empty_typed" "assigned_free_vars_seq_store_empty";
val _ = emit "assigned_vars_nested_decs_append_typed" "assigned_vars_nested_decs_append";
val _ = emit "nested_seq_assigned_vars_eq_typed" "nested_seq_assigned_vars_eq";
val _ = emit "assigned_vars_store_globals_empty_typed" "assigned_vars_store_globals_empty";
val _ = emit "assigned_vars_seq_store_empty_typed" "assigned_vars_seq_store_empty";
val _ = emit "every_exp_def_typed" "every_exp_def";
val _ = emit "var_exp_load_shape_typed" "var_exp_load_shape";
val _ = emit "exps_of_def_typed" "exps_of_def";
val _ = emit "evaluate_io_events_mono_typed" "evaluate_io_events_mono";
val _ = emit "sh_mem_load_FLOOKUP_locals_typed" "sh_mem_load_FLOOKUP_locals";
val _ = emit "sh_mem_store_FLOOKUP_locals_typed" "sh_mem_store_FLOOKUP_locals";
val _ = emit "unassigned_free_vars_evaluate_same_typed" "unassigned_free_vars_evaluate_same";
val _ = emit "dec_clock_simp_typed" "dec_clock_simp";
val _ = emit "empty_locals_simp_typed" "empty_locals_simp";
val _ = emit "eval_upd_clock_eq_typed" "eval_upd_clock_eq";
val _ = emit "opt_mmap_eval_upd_clock_eq_typed" "opt_mmap_eval_upd_clock_eq";
val _ = emit "eval_load_shape_el_rel_typed" "eval_load_shape_el_rel";
val _ = emit "evaluate_code_invariant_typed" "evaluate_code_invariant";
val _ = emit "evaluate_seq_store_globals_res_typed" "evaluate_seq_store_globals_res";
val _ = emit "evaluate_seq_stroes_locals_eq_typed" "evaluate_seq_stroes_locals_eq";
val _ = emit "evaluate_seq_stores_mem_state_rel_typed" "evaluate_seq_stores_mem_state_rel";
val _ = emit "flookup_res_var_diff_eq_typed" "flookup_res_var_diff_eq";
val _ = emit "flookup_res_var_distinct_zip_eq_typed" "flookup_res_var_distinct_zip_eq";
val _ = emit "flookup_res_var_thm_typed" "flookup_res_var_thm";
val _ = emit "FLOOKUP_set_globals_typed" "FLOOKUP_set_globals";
val _ = emit "length_load_shape_eq_shape_typed" "length_load_shape_eq_shape";
val _ = emit "var_cexp_load_globals_empty_typed" "var_cexp_load_globals_empty";
val _ = emit "el_load_globals_elem_typed" "el_load_globals_elem";
val _ = emit "length_load_globals_eq_read_size_typed" "length_load_globals_eq_read_size";
val _ = emit "lookup_locals_eq_map_vars_typed" "lookup_locals_eq_map_vars";
val _ = emit "map_var_cexp_eq_var_typed" "map_var_cexp_eq_var";
val _ = emit "res_var_lookup_original_eq_typed" "res_var_lookup_original_eq";
val _ = emit "update_locals_not_vars_eval_eq_typed" "update_locals_not_vars_eval_eq";
val _ = emit "eval_some_var_cexp_local_lookup_typed" "eval_some_var_cexp_local_lookup";
val _ = emit "opt_mmap_eval_some_var_cexp_local_lookup_typed" "opt_mmap_eval_some_var_cexp_local_lookup";
val _ = emit "evaluate_add_clock_eq_typed" "evaluate_add_clock_eq";
val _ = emit "evaluate_add_clock_io_events_mono_typed" "evaluate_add_clock_io_events_mono";
val _ = emit "mem_load_flat_rel_typed" "mem_load_flat_rel";
