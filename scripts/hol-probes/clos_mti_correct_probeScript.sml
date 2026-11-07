load "clos_mtiProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show_thm label th =
  if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show_thm "evaluate_apps_def=" clos_mtiProofTheory.evaluate_apps_def;
val _ = show_thm "evaluate_intro_multi=" clos_mtiProofTheory.evaluate_intro_multi;
val _ = show_thm "intro_multi_correct=" clos_mtiProofTheory.intro_multi_correct;
val _ = show_thm "semantics_intro_multi=" clos_mtiProofTheory.semantics_intro_multi;
val _ = show_thm "semantics_compile=" clos_mtiProofTheory.semantics_compile;
val _ = show_thm "contains_App_SOME_intro_multi=" clos_mtiProofTheory.contains_App_SOME_intro_multi;
val _ = show_thm "every_Fn_vs_NONE_intro_multi=" clos_mtiProofTheory.every_Fn_vs_NONE_intro_multi;
val _ = show_thm "contains_App_SOME_collect_args=" clos_mtiProofTheory.contains_App_SOME_collect_args;
val _ = show_thm "contains_App_SOME_collect_apps=" clos_mtiProofTheory.contains_App_SOME_collect_apps;
