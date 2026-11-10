(* Typed source definitions for the balanced switch construction in
   cakeml/compiler/backend/bvl_jumpScript.sml. *)
load "bvl_jumpTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");

val _ = show "JumpList_def_typed" bvl_jumpTheory.JumpList_def;
val _ = show "Jump_def_typed" bvl_jumpTheory.Jump_def;
