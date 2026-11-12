(* Typed source declarations for bvlProps (task 148). *)
load "preamble";
load "bvlPropsTheory";
open HolKernel Parse boolLib bossLib;
open preamble bvlPropsTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="bvlProps",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by bvlProps")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of bvlProps")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "get_code_labels_def_typed" "get_code_labels_def";
val _ = emit "find_code_EVERY_IMP_typed" "find_code_EVERY_IMP";
val _ = emit "do_app_err_typed" "do_app_err";
val _ = emit "evaluate_CONS_typed" "evaluate_CONS";
val _ = emit "evaluate_APPEND_typed" "evaluate_APPEND";
val _ = emit "evaluate_SNOC_typed" "evaluate_SNOC";
val _ = emit "evaluate_LENGTH_typed" "evaluate_LENGTH";
val _ = emit "evaluate_IMP_LENGTH_typed" "evaluate_IMP_LENGTH";
val _ = emit "evaluate_SING_typed" "evaluate_SING";
val _ = emit "do_app_change_clock_typed" "do_app_change_clock";
val _ = emit "do_app_change_clock_err_typed" "do_app_change_clock_err";
val _ = emit "do_app_io_events_mono_typed" "do_app_io_events_mono";
val _ = emit "inc_clock_def_typed" "inc_clock_def";
val _ = emit "evaluate_add_clock_typed" "evaluate_add_clock";
val _ = emit "evaluate_io_events_mono_typed" "evaluate_io_events_mono";
val _ = emit "evaluate_add_to_clock_io_events_mono_typed" "evaluate_add_to_clock_io_events_mono";
val _ = emit "do_app_with_code_typed" "do_app_with_code";
val _ = emit "do_app_with_code_err_not_Install_typed" "do_app_with_code_err_not_Install";
val _ = emit "do_app_Rval_swap_typed" "do_app_Rval_swap";
val _ = emit "do_app_Rerr_swap_typed" "do_app_Rerr_swap";
val _ = emit "evaluate_mk_tick_typed" "evaluate_mk_tick";
val _ = emit "evaluate_mono_typed" "evaluate_mono";
val _ = emit "evaluate_expand_env_typed" "evaluate_expand_env";
val _ = emit "isVar_def_typed" "isVar_def";
val _ = emit "bVarBound_def_typed" "bVarBound_def";
val _ = emit "do_app_refs_SUBSET_typed" "do_app_refs_SUBSET";
val _ = emit "evaluate_refs_SUBSET_typed" "evaluate_refs_SUBSET";
