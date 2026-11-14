(* Typed source declarations for evaluateProps (task 148). *)
load "preamble";
load "evaluatePropsTheory";
open HolKernel Parse boolLib bossLib;
open preamble evaluatePropsTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="evaluateProps",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by evaluateProps")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of evaluateProps")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "evaluate_nil_typed" "evaluate_nil";
val _ = emit "evaluate_next_type_stamp_mono_typed" "evaluate_next_type_stamp_mono";
val _ = emit "evaluate_next_exn_stamp_mono_typed" "evaluate_next_exn_stamp_mono";
val _ = emit "evaluate_refs_length_mono_typed" "evaluate_refs_length_mono";
val _ = emit "eval_no_eval_simulation_typed" "eval_no_eval_simulation";
val _ = emit "evaluate_length_typed" "evaluate_length";
val _ = emit "evaluate_sing_typed" "evaluate_sing";
val _ = emit "evaluate_decs_cons_typed" "evaluate_decs_cons";
val _ = emit "evaluate_decs_append_typed" "evaluate_decs_append";
val _ = emit "call_FFI_rel_def_typed" "call_FFI_rel_def";
val _ = emit "call_FFI_LENGTH_typed" "call_FFI_LENGTH";
val _ = emit "call_FFI_rel_consts_typed" "call_FFI_rel_consts";
val _ = emit "RTC_call_FFI_rel_consts_typed" "RTC_call_FFI_rel_consts";
val _ = emit "io_events_mono_def_typed" "io_events_mono_def";
val _ = emit "io_events_mono_refl_typed" "io_events_mono_refl";
val _ = emit "io_events_mono_trans_typed" "io_events_mono_trans";
val _ = emit "io_events_mono_antisym_typed" "io_events_mono_antisym";
val _ = emit "call_FFI_rel_io_events_mono_typed" "call_FFI_rel_io_events_mono";
val _ = emit "do_app_call_FFI_rel_typed" "do_app_call_FFI_rel";
val _ = emit "do_app_io_events_mono_typed" "do_app_io_events_mono";
val _ = emit "evaluate_call_FFI_rel_typed" "evaluate_call_FFI_rel";
val _ = emit "evaluate_io_events_mono_typed" "evaluate_io_events_mono";
val _ = emit "evaluate_call_FFI_rel_imp_typed" "evaluate_call_FFI_rel_imp";
val _ = emit "evaluate_decs_call_FFI_rel_imp_typed" "evaluate_decs_call_FFI_rel_imp";
val _ = emit "evaluate_io_events_mono_imp_typed" "evaluate_io_events_mono_imp";
val _ = emit "is_clock_io_mono_def_typed" "is_clock_io_mono_def";
val _ = emit "is_clock_io_mono_return_typed" "is_clock_io_mono_return";
val _ = emit "is_clock_io_mono_err_typed" "is_clock_io_mono_err";
val _ = emit "is_clock_io_mono_cong_typed" "is_clock_io_mono_cong";
val _ = emit "is_clock_io_mono_extra_typed" "is_clock_io_mono_extra";
val _ = emit "is_clock_io_mono_extra_mono_typed" "is_clock_io_mono_extra_mono";
val _ = emit "adj_clock_def_typed" "adj_clock_def";
val _ = emit "dec_inc_clock_typed" "dec_inc_clock";
val _ = emit "is_clock_io_mono_check_typed" "is_clock_io_mono_check";
val _ = emit "is_clock_io_mono_bind_typed" "is_clock_io_mono_bind";
val _ = emit "do_app_refs_length_typed" "do_app_refs_length";
val _ = emit "is_clock_io_mono_do_app_simple_typed" "is_clock_io_mono_do_app_simple";
val _ = emit "is_clock_io_mono_acc_safe_typed" "is_clock_io_mono_acc_safe";
val _ = emit "is_clock_io_mono_if_safe_typed" "is_clock_io_mono_if_safe";
val _ = emit "is_clock_io_mono_option_case_safe_typed" "is_clock_io_mono_option_case_safe";
val _ = emit "is_clock_io_mono_match_case_safe_typed" "is_clock_io_mono_match_case_safe";
val _ = emit "is_clock_io_mono_match_case_pair_safe_typed" "is_clock_io_mono_match_case_pair_safe";
val _ = emit "is_clock_io_mono_evaluate_typed" "is_clock_io_mono_evaluate";
val _ = emit "is_clock_io_mono_evaluate_decs_typed" "is_clock_io_mono_evaluate_decs";
val _ = emit "evaluate_add_to_clock_typed" "evaluate_add_to_clock";
val _ = emit "evaluate_match_add_to_clock_typed" "evaluate_match_add_to_clock";
val _ = emit "evaluate_decs_add_to_clock_typed" "evaluate_decs_add_to_clock";
val _ = emit "evaluate_add_to_clock_io_events_mono_typed" "evaluate_add_to_clock_io_events_mono";
val _ = emit "evaluate_decs_add_to_clock_io_events_mono_typed" "evaluate_decs_add_to_clock_io_events_mono";
val _ = emit "evaluate_decs_ffi_mono_clock_typed" "evaluate_decs_ffi_mono_clock";
val _ = emit "evaluate_decs_clock_determ_typed" "evaluate_decs_clock_determ";
