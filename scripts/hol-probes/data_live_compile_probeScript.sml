(* Typed source definitions for the data-language liveness pass in
   cakeml/compiler/backend/data_liveScript.sml. *)
load "data_liveTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");

val _ = show "is_pure_def_typed" data_liveTheory.is_pure_def;
val _ = show "compile_def_typed" data_liveTheory.compile_def;
load "data_liveProofTheory";
val _ = show "get_code_labels_compile_typed" data_liveProofTheory.get_code_labels_compile;
