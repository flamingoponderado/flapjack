(* Typed source definitions for the tick constructor and canonical wrapper
   check in cakeml/compiler/backend/bvi_inlineScript.sml. *)
load "bvi_inlineTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");

val _ = show "bvi_mk_tick_def_typed" bvi_inlineTheory.bvi_mk_tick_def;
val _ = show "canonical_wrapper_def_typed" bvi_inlineTheory.canonical_wrapper_def;
