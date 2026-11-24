(* Typed source declarations for the result relations in
   semantics/proofs/semanticPrimitivesPropsScript.sml (task 273). *)
load "preamble";
load "semanticPrimitivesPropsTheory";
open HolKernel Parse boolLib bossLib;
open preamble semanticPrimitivesPropsTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy = "semanticPrimitivesProps", Name = name};

fun show label th =
  (print (label ^ "=");
   app (fn h => (print_term h; print " ==> ")) (hyp th);
   print_term (concl th);
   print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by semanticPrimitivesProps")
  | SOME (th, _) => show label th;

val _ = emit "exc_rel_raise1_typed" "exc_rel_raise1";
val _ = emit "exc_rel_raise2_typed" "exc_rel_raise2";
val _ = emit "exc_rel_type_error1_typed" "exc_rel_type_error1";
val _ = emit "exc_rel_type_error2_typed" "exc_rel_type_error2";
val _ = emit "exc_rel_refl_typed" "exc_rel_refl";
val _ = emit "exc_rel_trans_typed" "exc_rel_trans";
val _ = emit "result_rel_Rval_typed" "result_rel_Rval";
val _ = emit "result_rel_Rerr1_typed" "result_rel_Rerr1";
val _ = emit "result_rel_Rerr2_typed" "result_rel_Rerr2";
val _ = emit "result_rel_refl_typed" "result_rel_refl";
val _ = emit "result_rel_trans_typed" "result_rel_trans";
