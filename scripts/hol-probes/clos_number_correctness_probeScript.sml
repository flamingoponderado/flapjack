(* Typed source statements for closure numbering correctness. *)
load "clos_numberProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then
  (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "v_rel_rules_typed=" clos_numberProofTheory.v_rel_rules;
val _ = show "state_rel_typed=" clos_numberProofTheory.state_rel_def;
val _ = show "renumber_correct_typed=" clos_numberProofTheory.renumber_code_locs_correct;
val _ = show "semantics_number_typed=" clos_numberProofTheory.semantics_number;
