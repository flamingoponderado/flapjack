(* Typed source declarations for pattern_semantics (task 148). *)
load "preamble";
load "pattern_semanticsTheory";
open HolKernel Parse boolLib bossLib;
open preamble pattern_semanticsTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="pattern_semantics",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by pattern_semantics")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of pattern_semantics")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = dt_label "term_typed" "term";
val _ = emit "dt_test_def_typed" "dt_test_def";
val _ = dt_label "pat_typed" "pat";
val _ = dt_label "dTest_typed" "dTest";
val _ = dt_label "dGuard_typed" "dGuard";
val _ = dt_label "dTree_typed" "dTree";
val _ = emit "is_sibling_def_typed" "is_sibling_def";
val _ = emit "pmatch_def_typed" "pmatch_def";
val _ = emit "match_def_typed" "match_def";
val _ = emit "app_pos_def_typed" "app_pos_def";
val _ = emit "dt_eval_guard_def_typed" "dt_eval_guard_def";
val _ = emit "dt_eval_def_typed" "dt_eval_def";
