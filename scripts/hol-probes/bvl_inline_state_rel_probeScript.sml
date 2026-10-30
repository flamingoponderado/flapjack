(* Typed original tick-removal state relation. *)
load "bvl_inlineProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "state_rel=" bvl_inlineProofTheory.state_rel_def;
