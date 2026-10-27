load "source_to_flatProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show_type label tm = (print label; print_type (type_of tm); print "\n");
fun show_thm label th =
  if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show_type "value_rel_type=" ``source_to_flatProof$v_rel``;
val _ = show_type "env_rel_type=" ``source_to_flatProof$env_rel``;
val _ = show_type "global_inv_type=" ``source_to_flatProof$global_env_inv``;
val _ = show_thm "value_rel_rules=" source_to_flatProofTheory.v_rel_rules;
