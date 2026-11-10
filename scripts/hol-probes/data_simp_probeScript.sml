(* Typed source definitions for the data-language sequence simplifier in
   cakeml/compiler/backend/data_simpScript.sml. *)
load "data_simpTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");

val _ = show "pSeq_def_typed" data_simpTheory.pSeq_def;
val _ = show "simp_def_typed" data_simpTheory.simp_def;
