(* Typed source declarations for dataProps (task 148). *)
load "preamble";
load "dataPropsTheory";
open HolKernel Parse boolLib bossLib;
open preamble dataPropsTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="dataProps",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by dataProps")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of dataProps")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "pop_env_const_typed" "pop_env_const";
val _ = emit "pop_env_safe_for_space_typed" "pop_env_safe_for_space";
val _ = emit "do_app_io_events_mono_typed" "do_app_io_events_mono";
val _ = emit "do_app_stack_max_typed" "do_app_stack_max";
val _ = emit "do_app_safe_for_space_mono_typed" "do_app_safe_for_space_mono";
val _ = emit "evaluate_io_events_mono_typed" "evaluate_io_events_mono";
val _ = emit "evaluate_safe_for_space_mono_typed" "evaluate_safe_for_space_mono";
val _ = emit "evaluate_option_le_stack_max_typed" "evaluate_option_le_stack_max";
val _ = emit "do_app_aux_const_typed" "do_app_aux_const";
val _ = emit "do_app_const_typed" "do_app_const";
val _ = emit "do_app_aux_err_typed" "do_app_aux_err";
val _ = emit "do_app_err_typed" "do_app_err";
val _ = emit "EVERY_get_vars_typed" "EVERY_get_vars";
val _ = emit "get_vars_IMP_domain_typed" "get_vars_IMP_domain";
val _ = emit "get_vars_append_typed" "get_vars_append";
val _ = emit "get_vars_reverse_typed" "get_vars_reverse";
val _ = emit "var_corr_def_typed" "var_corr_def";
val _ = emit "get_vars_thm_typed" "get_vars_thm";
val _ = emit "get_code_labels_def_typed" "get_code_labels_def";
val _ = emit "cut_state_opt_with_const_typed" "cut_state_opt_with_const";
val _ = emit "do_app_aux_with_locals_typed" "do_app_aux_with_locals";
val _ = emit "do_app_aux_with_space_typed" "do_app_aux_with_space";
val _ = emit "consume_space_add_space_typed" "consume_space_add_space";
val _ = emit "same_stack_size_def_typed" "same_stack_size_def";
val _ = emit "same_stack_size_size_of_stack_typed" "same_stack_size_size_of_stack";
val _ = emit "s_peak_heap_typed" "s_peak_heap";
val _ = emit "evaluate_smx_safe_peak_swap_aux_typed" "evaluate_smx_safe_peak_swap_aux";
val _ = emit "evaluate_smx_safe_peak_swap_typed" "evaluate_smx_safe_peak_swap";
val _ = emit "evaluate_safe_peak_swap_aux_typed" "evaluate_safe_peak_swap_aux";
val _ = emit "evaluate_safe_peak_swap_typed" "evaluate_safe_peak_swap";
val _ = emit "do_app_safe_peak_swap_typed" "do_app_safe_peak_swap";
val _ = emit "do_app_sm_safe_peak_swap_typed" "do_app_sm_safe_peak_swap";
val _ = emit "do_app_aux_safe_peak_swap_typed" "do_app_aux_safe_peak_swap";
val _ = emit "do_app_aux_sm_safe_peak_swap_typed" "do_app_aux_sm_safe_peak_swap";
val _ = emit "do_app_err_safe_peak_swap_typed" "do_app_err_safe_peak_swap";
val _ = emit "do_app_err_sm_safe_peak_swap_typed" "do_app_err_sm_safe_peak_swap";
val _ = emit "size_of_heap_with_safe_typed" "size_of_heap_with_safe";
val _ = emit "OPTION_MAP2_ADD_SOME_0_typed" "OPTION_MAP2_ADD_SOME_0";
val _ = emit "OPTION_MAP2_MAX_CANCEL_typed" "OPTION_MAP2_MAX_CANCEL";
val _ = emit "OPTION_MAP2_NONE_typed" "OPTION_MAP2_NONE";
val _ = emit "initial_state_simp_typed" "initial_state_simp";
val _ = emit "initial_state_with_simp_typed" "initial_state_with_simp";
val _ = emit "with_same_locals_typed" "with_same_locals";
val _ = emit "do_stack_const_typed" "do_stack_const";
val _ = emit "Seq_Skip_typed" "Seq_Skip";
val _ = emit "do_space_alt_typed" "do_space_alt";
val _ = emit "evaluate_safe_alt_typed" "evaluate_safe_alt";
val _ = emit "evaluate_peak_alt_typed" "evaluate_peak_alt";
val _ = emit "set_var_const_typed" "set_var_const";
val _ = emit "set_var_with_const_typed" "set_var_with_const";
val _ = emit "set_vars_const_typed" "set_vars_const";
val _ = emit "set_vars_with_const_typed" "set_vars_with_const";
val _ = emit "call_env_const_typed" "call_env_const";
val _ = emit "call_env_with_const_typed" "call_env_with_const";
val _ = emit "push_env_const_typed" "push_env_const";
val _ = emit "push_env_with_const_typed" "push_env_with_const";
val _ = emit "dec_clock_const_typed" "dec_clock_const";
val _ = emit "add_space_const_typed" "add_space_const";
val _ = emit "with_clock_ffi_typed" "with_clock_ffi";
val _ = emit "with_same_clock_typed" "with_same_clock";
val _ = emit "cut_state_eq_some_typed" "cut_state_eq_some";
val _ = emit "cut_state_eq_none_typed" "cut_state_eq_none";
val _ = emit "size_of_heap_with_clock_typed" "size_of_heap_with_clock";
val _ = emit "size_of_heap_args_with_clock_typed" "size_of_heap_args_with_clock";
val _ = emit "do_app_Rerr_typed" "do_app_Rerr";
val _ = emit "pop_env_with_const_typed" "pop_env_with_const";
val _ = emit "jump_exc_with_const_typed" "jump_exc_with_const";
val _ = emit "cut_state_opt_const_typed" "cut_state_opt_const";
val _ = emit "Boolv_11_typed" "Boolv_11";
val _ = emit "do_app_with_clock_typed" "do_app_with_clock";
val _ = emit "do_app_change_clock_typed" "do_app_change_clock";
val _ = emit "space_consumed_with_clock_typed" "space_consumed_with_clock";
