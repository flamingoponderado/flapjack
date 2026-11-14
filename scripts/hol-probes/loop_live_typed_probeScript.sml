(* Typed source declarations for loop_live (task 148). *)
load "preamble";
load "loop_liveTheory";
open HolKernel Parse boolLib bossLib;
open preamble loop_liveTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="loop_live",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by loop_live")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of loop_live")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "arith_vars_typed" "arith_vars";
val _ = emit "comp_def_typed" "comp_def";
val _ = emit "mark_all_def_typed" "mark_all_def";
val _ = emit "optimise_def_typed" "optimise_def";
val _ = emit "shrink_def_typed" "shrink_def";
val _ = emit "size_inter_typed" "size_inter";
val _ = emit "size_mk_BN_typed" "size_mk_BN";
val _ = emit "size_mk_BS_typed" "size_mk_BS";
val _ = emit "vars_of_exp_def_typed" "vars_of_exp_def";
val _ = emit "fixedpoint_thm_typed" "fixedpoint_thm";
