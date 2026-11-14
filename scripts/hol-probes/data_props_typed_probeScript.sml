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
