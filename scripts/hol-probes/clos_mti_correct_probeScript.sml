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
(* These local theorems are not exported: replay their original statements
   and proofs with typed printing enabled. *)
load "preamble";
open preamble clos_mtiTheory closPropsTheory;
val every_Fn_vs_NONE_collect_apps_replay = prove (
  ``∀max_app es e x y. collect_apps max_app es e = (x,y) ⇒
    (every_Fn_vs_NONE x ∧ every_Fn_vs_NONE [y] ⇔
     every_Fn_vs_NONE es ∧ every_Fn_vs_NONE [e])``,
  ho_match_mp_tac collect_apps_ind >>
  srw_tac[][collect_apps_def] >> full_simp_tac(srw_ss())[] >>
  ONCE_REWRITE_TAC[every_Fn_vs_NONE_EVERY] >>
  srw_tac[][] >> metis_tac[]);
val every_Fn_vs_NONE_collect_args_replay = prove (
  ``∀max_app es e x y. collect_args max_app es e = (x,y) ⇒
    (every_Fn_vs_NONE [y] ⇔ every_Fn_vs_NONE [e])``,
  ho_match_mp_tac collect_args_ind >>
  srw_tac[][collect_args_def] >> full_simp_tac(srw_ss())[]);
val _ = show_thm "every_Fn_vs_NONE_collect_apps_replay=" every_Fn_vs_NONE_collect_apps_replay;
val _ = show_thm "every_Fn_vs_NONE_collect_args_replay=" every_Fn_vs_NONE_collect_args_replay;
val _ = show_thm "collect_apps_no_Labels=" clos_mtiProofTheory.collect_apps_no_Labels;
val _ = show_thm "collect_args_no_Labels=" clos_mtiProofTheory.collect_args_no_Labels;
val _ = show_thm "EVERY_intro_multi=" clos_mtiProofTheory.EVERY_intro_multi;
val _ = show_thm "HD_intro_multi=" clos_mtiProofTheory.HD_intro_multi;
val _ = show_thm "intro_multi_cons=" clos_mtiProofTheory.intro_multi_cons;
val _ = show_thm "intro_multi_no_Labels=" clos_mtiProofTheory.intro_multi_no_Labels;
val _ = show_thm "intro_multi_obeys_max_app=" clos_mtiProofTheory.intro_multi_obeys_max_app;
val _ = show_thm "collect_args_preserves_set_globals=" clos_mtiProofTheory.collect_args_preserves_set_globals;
val _ = show_thm "collect_args_preserves_esgc_free=" clos_mtiProofTheory.collect_args_preserves_esgc_free;
val _ = show_thm "collect_apps_preserves_set_globals=" clos_mtiProofTheory.collect_apps_preserves_set_globals;
val _ = show_thm "collect_apps_preserves_esgc_free=" clos_mtiProofTheory.collect_apps_preserves_esgc_free;
