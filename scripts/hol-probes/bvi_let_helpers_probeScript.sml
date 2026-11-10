(* Typed source definitions for the BVI let-propagation helpers in
   cakeml/compiler/backend/bvi_letScript.sml. *)
load "bvi_letTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");

val _ = show "extract_def_typed" bvi_letTheory.extract_def;
val _ = show "extract_list_def_typed" bvi_letTheory.extract_list_def;
val _ = show "delete_var_def_typed" bvi_letTheory.delete_var_def;
