(* Typed source definitions for the allocation-space pass in
   cakeml/compiler/backend/data_spaceScript.sml. *)
load "data_spaceTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");

val _ = show "pMakeSpace_def_typed" data_spaceTheory.pMakeSpace_def;
val _ = show "space_def_typed" data_spaceTheory.space_def;
val _ = show "compile_def_typed" data_spaceTheory.compile_def;
