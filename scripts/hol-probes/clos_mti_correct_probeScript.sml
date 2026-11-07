load "clos_mtiProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show_thm label th =
  if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show_thm "evaluate_intro_multi=" clos_mtiProofTheory.evaluate_intro_multi;
val _ = show_thm "intro_multi_correct=" clos_mtiProofTheory.intro_multi_correct;
val _ = show_thm "semantics_intro_multi=" clos_mtiProofTheory.semantics_intro_multi;
val _ = show_thm "semantics_compile=" clos_mtiProofTheory.semantics_compile;
