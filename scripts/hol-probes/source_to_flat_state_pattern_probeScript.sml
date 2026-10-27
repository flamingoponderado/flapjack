load "source_to_flatProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show_thm label th =
  if null (hyp th) then (print label; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show_thm "store_rel_rules=" source_to_flatProofTheory.sv_rel_rules;
val _ = show_thm "state_rel_rules=" source_to_flatProofTheory.s_rel_rules;
val _ = show_thm "state_rel_cases=" source_to_flatProofTheory.s_rel_cases;
val _ = show_thm "match_result_def=" source_to_flatProofTheory.match_result_rel_def;
val _ = show_thm "match_result_imp=" source_to_flatProofTheory.match_result_rel_imp;
