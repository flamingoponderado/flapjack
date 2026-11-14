(* Typed source declarations for flatSem (task 148). *)
load "preamble";
load "flatSemTheory";
open HolKernel Parse boolLib bossLib;
open preamble flatSemTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="flatSem",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by flatSem")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of flatSem")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "semantics_def_typed" "semantics_def";
val _ = emit "evaluate_clock_typed" "evaluate_clock";
val _ = emit "fix_clock_evaluate_typed" "fix_clock_evaluate";
val _ = emit "evaluate_def_typed" "evaluate_def";
val _ = emit "do_app_def_typed" "do_app_def";
val _ = emit "initial_state_def_typed" "initial_state_def";
val _ = dt_label "environment_typed" "environment";
val _ = dt_label "v_typed" "v";
val _ = dt_label "install_config_typed" "install_config";
val _ = dt_label "state_typed" "state";
val _ = emit "list_id_def_typed" "list_id_def";
val _ = emit "Boolv_def_typed" "Boolv_def";
val _ = emit "Unitv_def_typed" "Unitv_def";
val _ = emit "build_rec_env_def_typed" "build_rec_env_def";
val _ = emit "ctor_same_type_def_typed" "ctor_same_type_def";
val _ = emit "do_eq_def_typed" "do_eq_def";
val _ = emit "do_opapp_def_typed" "do_opapp_def";
val _ = emit "v_to_list_def_typed" "v_to_list_def";
val _ = emit "list_to_v_def_typed" "list_to_v_def";
val _ = emit "v_to_char_list_def_typed" "v_to_char_list_def";
val _ = emit "vs_to_string_def_typed" "vs_to_string_def";
val _ = emit "check_type_def_typed" "check_type_def";
val _ = emit "dest_Litv_def_typed" "dest_Litv_def";
val _ = emit "v_to_flat_def_typed" "v_to_flat_def";
val _ = emit "flat_to_v_def_typed" "flat_to_v_def";
val _ = emit "do_test_def_typed" "do_test_def";
val _ = emit "bind_exn_v_def_typed" "bind_exn_v_def";
val _ = emit "chr_exn_v_def_typed" "chr_exn_v_def";
val _ = emit "div_exn_v_def_typed" "div_exn_v_def";
val _ = emit "subscript_exn_v_def_typed" "subscript_exn_v_def";
val _ = emit "pmatch_def_typed" "pmatch_def";
val _ = emit "pmatch_rows_def_typed" "pmatch_rows_def";
val _ = emit "do_if_def_typed" "do_if_def";
val _ = emit "do_if_either_or_typed" "do_if_either_or";
val _ = emit "AppUnit_def_typed" "AppUnit_def";
val _ = emit "dec_clock_def_typed" "dec_clock_def";
val _ = emit "fix_clock_def_typed" "fix_clock_def";
val _ = emit "v_to_bytes_def_typed" "v_to_bytes_def";
val _ = emit "v_to_words_def_typed" "v_to_words_def";
val _ = emit "do_eval_def_typed" "do_eval_def";
val _ = dt_label "dest_thunk_ret_typed" "dest_thunk_ret";
val _ = emit "dest_thunk_def_typed" "dest_thunk_def";
val _ = emit "update_thunk_def_typed" "update_thunk_def";
val _ = emit "bad_thunk_update_def_typed" "bad_thunk_update_def";
val _ = emit "do_app_const_typed" "do_app_const";
