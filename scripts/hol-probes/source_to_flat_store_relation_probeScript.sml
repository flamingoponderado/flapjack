load "source_to_flatProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show_thm label th =
  if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show_thm "store_relation_rules=" source_to_flatProofTheory.sv_rel_rules;
val _ = show_thm "state_relation_rule=" source_to_flatProofTheory.s_rel_rules;
