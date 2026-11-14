(* Typed source declarations for evaluate (task 148). *)
load "preamble";
load "evaluateTheory";
open HolKernel Parse boolLib bossLib;
open preamble evaluateTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="evaluate",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by evaluate")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of evaluate")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "evaluate_def_typed" "evaluate_def";
val _ = emit "full_evaluate_ind_typed" "full_evaluate_ind";
val _ = emit "evaluate_clock_typed" "evaluate_clock";
val _ = emit "fix_clock_evaluate_typed" "fix_clock_evaluate";
val _ = emit "full_evaluate_def_typed" "full_evaluate_def";
val _ = emit "dec_clock_def_typed" "dec_clock_def";
val _ = emit "fix_clock_def_typed" "fix_clock_def";
val _ = emit "fix_clock_do_eval_res_typed" "fix_clock_do_eval_res";
val _ = emit "list_result_def_typed" "list_result_def";
val _ = emit "sing_env_def_typed" "sing_env_def";
val _ = emit "do_eval_res_def_typed" "do_eval_res_def";
