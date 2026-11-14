(* Typed source declarations for flatProps (task 148). *)
load "preamble";
load "flatPropsTheory";
open HolKernel Parse boolLib bossLib;
open preamble flatPropsTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="flatProps",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by flatProps")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of flatProps")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "mk_flat_install_conf_def_typed" "mk_flat_install_conf_def";
val _ = emit "pmatch_bindings_typed" "pmatch_bindings";
val _ = emit "evaluate_decs_append_typed" "evaluate_decs_append";
val _ = emit "build_rec_env_eq_MAP_typed" "build_rec_env_eq_MAP";
val _ = emit "simple_basic_val_rel_def_typed" "simple_basic_val_rel_def";
val _ = emit "evaluate_match_def_typed" "evaluate_match_def";
val _ = emit "v_container_xs_def_typed" "v_container_xs_def";
val _ = emit "elist_globals_eq_empty_typed" "elist_globals_eq_empty";
val _ = emit "op_gbag_def_typed" "op_gbag_def";
val _ = emit "set_globals_def_typed" "set_globals_def";
val _ = emit "esgc_free_def_typed" "esgc_free_def";
val _ = emit "eval_sim_def_typed" "eval_sim_def";
val _ = emit "evaluate_length_typed" "evaluate_length";
val _ = emit "evaluate_sing_typed" "evaluate_sing";
val _ = emit "result_vs_def_typed" "result_vs_def";
val _ = emit "no_Mat_def_typed" "no_Mat_def";
val _ = emit "no_Mat_decs_def_typed" "no_Mat_decs_def";
val _ = emit "isClosure_def_typed" "isClosure_def";
val _ = emit "simple_val_rel_def_typed" "simple_val_rel_def";
val _ = emit "simple_state_rel_def_typed" "simple_state_rel_def";
val _ = emit "simple_val_rel_rew_typed" "simple_val_rel_rew";
val _ = emit "simple_val_rel_simps_typed" "simple_val_rel_simps";
val _ = emit "simple_val_rel_isClosure_typed" "simple_val_rel_isClosure";
val _ = emit "simple_do_eq_thm_ind_typed" "simple_do_eq_thm_ind";
val _ = emit "simple_do_eq_thm_typed" "simple_do_eq_thm";
val _ = emit "simple_state_rel_store_assign_typed" "simple_state_rel_store_assign";
val _ = emit "simple_state_rel_store_alloc_typed" "simple_state_rel_store_alloc";
val _ = emit "simple_state_rel_store_lookup_typed" "simple_state_rel_store_lookup";
val _ = emit "elist_globals_append_typed" "elist_globals_append";
val _ = emit "simple_v_rel_list_to_v_typed" "simple_v_rel_list_to_v";
val _ = emit "simple_vs_to_string_v_rel_typed" "simple_vs_to_string_v_rel";
val _ = emit "pmatch_rows_IMP_pmatch_typed" "pmatch_rows_IMP_pmatch";
val _ = emit "simple_v_to_char_list_v_rel_typed" "simple_v_to_char_list_v_rel";
val _ = emit "simple_v_to_list_v_rel_typed" "simple_v_to_list_v_rel";
val _ = emit "simple_val_rel_v_to_words_typed" "simple_val_rel_v_to_words";
val _ = emit "simple_val_rel_v_to_bytes_typed" "simple_val_rel_v_to_bytes";
val _ = emit "pmatch_length_typed" "pmatch_length";
val _ = emit "do_app_state_unchanged_typed" "do_app_state_unchanged";
val _ = emit "pmatch_state_typed" "pmatch_state";
val _ = emit "pmatch_ignore_clock_typed" "pmatch_ignore_clock";
val _ = emit "pmatch_rows_ignore_clock_typed" "pmatch_rows_ignore_clock";
val _ = emit "pmatch_extend_typed" "pmatch_extend";
val _ = emit "pmatch_append_typed" "pmatch_append";
val _ = emit "pmatch_any_match_typed" "pmatch_any_match";
val _ = emit "pmatch_any_no_match_typed" "pmatch_any_no_match";
val _ = emit "pmatch_any_match_error_typed" "pmatch_any_match_error";
val _ = emit "pmatch_list_pairwise_typed" "pmatch_list_pairwise";
val _ = emit "pmatch_list_snoc_nil_typed" "pmatch_list_snoc_nil";
val _ = emit "pmatch_list_append_typed" "pmatch_list_append";
val _ = emit "pmatch_list_snoc_typed" "pmatch_list_snoc";
val _ = emit "map_match_eq_case_typed" "map_match_eq_case";
val _ = emit "pmatch_nil_typed" "pmatch_nil";
val _ = emit "build_rec_env_merge_typed" "build_rec_env_merge";
val _ = emit "evaluate_cons_typed" "evaluate_cons";
val _ = emit "evaluate_append_typed" "evaluate_append";
val _ = emit "with_clock_ffi_typed" "with_clock_ffi";
val _ = emit "evaluate_add_to_clock_typed" "evaluate_add_to_clock";
val _ = emit "evaluate_decs_add_to_clock_typed" "evaluate_decs_add_to_clock";
val _ = emit "do_app_io_events_mono_typed" "do_app_io_events_mono";
val _ = emit "store_v_vs_def_typed" "store_v_vs_def";
val _ = emit "ctor_same_type_OPTREL_typed" "ctor_same_type_OPTREL";
val _ = emit "pats_bindings_FLAT_MAP_typed" "pats_bindings_FLAT_MAP";
val _ = emit "evaluate_Mat_typed" "evaluate_Mat";
val _ = emit "evaluate_Handle_typed" "evaluate_Handle";
val _ = emit "evaluate_match_NIL_typed" "evaluate_match_NIL";
val _ = emit "evaluate_match_CONS_typed" "evaluate_match_CONS";
val _ = emit "simple_do_app_thm_typed" "simple_do_app_thm";
val _ = emit "isClosure_simps_typed" "isClosure_simps";
val _ = emit "evaluate_decs_add_to_clock_io_events_mono_alt_typed" "evaluate_decs_add_to_clock_io_events_mono_alt";
val _ = emit "elist_globals_FOLDR_typed" "elist_globals_FOLDR";
val _ = emit "elist_globals_REVERSE_typed" "elist_globals_REVERSE";
val _ = emit "initial_state_clock_typed" "initial_state_clock";
val _ = emit "IMP_semantics_eq_typed" "IMP_semantics_eq";
val _ = emit "pmatch_list_MAP_Pvar_typed" "pmatch_list_MAP_Pvar";
val _ = emit "evaluate_MAP_Var_local_typed" "evaluate_MAP_Var_local";
val _ = emit "bind_locals_list_def_typed" "bind_locals_list_def";
val _ = emit "evaluate_vars_typed" "evaluate_vars";
val _ = emit "evaluate_add_to_clock_io_events_mono_typed" "evaluate_add_to_clock_io_events_mono";
val _ = emit "evaluate_dec_add_to_clock_io_events_mono_typed" "evaluate_dec_add_to_clock_io_events_mono";
val _ = emit "evaluate_decs_add_to_clock_io_events_mono_typed" "evaluate_decs_add_to_clock_io_events_mono";
val _ = emit "evaluate_io_events_mono_typed" "evaluate_io_events_mono";
val _ = emit "evaluate_io_events_mono_IMP_typed" "evaluate_io_events_mono_IMP";
val _ = emit "evaluate_dec_io_events_mono_typed" "evaluate_dec_io_events_mono";
val _ = emit "evaluate_decs_io_events_mono_typed" "evaluate_decs_io_events_mono";
