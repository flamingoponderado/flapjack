(* Typed source declarations for bvl_const. *)
load "preamble";
load "bvl_constTheory";
open HolKernel Parse boolLib bossLib;
open preamble bvl_constTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");

val _ = show "dest_simple_pmatch_typed" bvl_constTheory.dest_simple_pmatch;
val _ = show "case_op_const_pmatch_typed" bvl_constTheory.case_op_const_pmatch;
val _ = show "SmartOp_flip_pmatch_typed" bvl_constTheory.SmartOp_flip_pmatch;
val _ = show "SmartOp2_pmatch_typed" bvl_constTheory.SmartOp2_pmatch;
val _ = show "dest_EqualInt_pmatch_typed" bvl_constTheory.dest_EqualInt_pmatch;
val _ = show "SmartOp_pmatch_typed" bvl_constTheory.SmartOp_pmatch;
val _ = show "extract_pmatch_typed" bvl_constTheory.extract_pmatch;
val _ = show "delete_var_pmatch_typed" bvl_constTheory.delete_var_pmatch;
val _ = show "compile_length_typed" bvl_constTheory.compile_length;
val _ = show "compile_HD_SING_typed" bvl_constTheory.compile_HD_SING;
