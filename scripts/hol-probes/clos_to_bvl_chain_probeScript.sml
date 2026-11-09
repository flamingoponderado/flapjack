load "clos_to_bvlProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show_thm label th =
  if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show_thm "chain_installed_def=" clos_to_bvlProofTheory.chain_installed_def;
val _ = show_thm "chain_installed_cons=" clos_to_bvlProofTheory.chain_installed_cons;
val _ = show_thm "chain_installed_SUBMAP=" clos_to_bvlProofTheory.chain_installed_SUBMAP;
val _ = show_thm "chain_installed_thm=" clos_to_bvlProofTheory.chain_installed_thm;
val _ = show_thm "chain_installed_chain_exps=" clos_to_bvlProofTheory.chain_installed_chain_exps;
val _ = show_thm "every_Fn_vs_SOME_def_typed=" closPropsTheory.every_Fn_vs_SOME_def;
val _ = show_thm "num_stubs_def_typed=" clos_to_bvlTheory.num_stubs_def;
val _ = show_thm "compile_prog_code_locs_typed=" clos_to_bvlProofTheory.compile_prog_code_locs;
val _ = show_thm "compile_exps_code_locs_typed=" clos_to_bvlProofTheory.compile_exps_code_locs;
val _ = show_thm "chain_exps_every_Fn_SOME_typed=" clos_to_bvlProofTheory.chain_exps_every_Fn_SOME;
(* The earlier theorem shares a HOL name with the later implication. *)
val chain_exps_every_Fn_SOME_8596_replay = Q.prove (
  `!x y. closProps$every_Fn_SOME (MAP (SND o SND) (clos_to_bvl$chain_exps x y)) <=> closProps$every_Fn_SOME y`,
  recInduct clos_to_bvlTheory.chain_exps_ind
  >> rw [clos_to_bvlTheory.chain_exps_def]
  >> pop_assum mp_tac
  >> once_rewrite_tac [rich_listTheory.CONS_APPEND]
  >> fs [closPropsTheory.every_Fn_SOME_APPEND]);
val _ = show_thm "chain_exps_every_Fn_SOME_8596_replay=" chain_exps_every_Fn_SOME_8596_replay;
val _ = show_thm "chain_exps_every_Fn_vs_SOME_typed=" clos_to_bvlProofTheory.chain_exps_every_Fn_vs_SOME;
val _ = show_thm "chain_exps_obeys_max_app_typed=" clos_to_bvlProofTheory.chain_exps_obeys_max_app;
val _ = show_thm "chain_exps_no_Labels_typed=" clos_to_bvlProofTheory.chain_exps_no_Labels;
