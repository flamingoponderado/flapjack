(* Typed source declarations for clos_op. *)
load "preamble";
load "clos_opTheory";
open HolKernel Parse boolLib bossLib;
open preamble clos_opTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");

val _ = show "dest_Const_pmatch_typed" clos_opTheory.dest_Const_pmatch;
val _ = show "dest_Constant_pmatch_typed" clos_opTheory.dest_Constant_pmatch;
val _ = show "dest_Cons_pmatch_typed" clos_opTheory.dest_Cons_pmatch;
val _ = show "dest_ElemAt_pmatch_typed" clos_opTheory.dest_ElemAt_pmatch;
val _ = show "dest_TagEq_pmatch_typed" clos_opTheory.dest_TagEq_pmatch;
val _ = show "dest_LenEq_pmatch_typed" clos_opTheory.dest_LenEq_pmatch;
val _ = show "dest_TagLenEq_pmatch_typed" clos_opTheory.dest_TagLenEq_pmatch;
val _ = show "dest_Op_pmatch_typed" clos_opTheory.dest_Op_pmatch;
val _ = show "is_Var_pmatch_typed" clos_opTheory.is_Var_pmatch;
