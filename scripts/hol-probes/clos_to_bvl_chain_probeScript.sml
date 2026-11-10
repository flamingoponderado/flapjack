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
val _ = show_thm "submap_rel_def_typed=" closPropsTheory.SUBMAP_rel_def;
val _ = show_thm "evaluate_code_submap_typed=" closPropsTheory.evaluate_code_SUBMAP;
val _ = show_thm "chain_exps_semantics_typed=" clos_to_bvlProofTheory.chain_exps_semantics;
val _ = show_thm "chain_exps_semantics_call_typed=" clos_to_bvlProofTheory.chain_exps_semantics_call;
val _ = show_thm "compile_every_Fn_SOME_typed=" clos_to_bvlProofTheory.compile_every_Fn_SOME;
val _ = show_thm "calls_preserves_every_Fn_vs_NONE_typed=" clos_callProofTheory.calls_preserves_every_Fn_vs_NONE;
val _ = show_thm "every_Fn_vs_NONE_cond_call_compile_inc_typed=" clos_to_bvlProofTheory.every_Fn_vs_NONE_cond_call_compile_inc;
val _ = show_thm "cl_rel_subspt_typed=" clos_to_bvlProofTheory.cl_rel_subspt;
val _ = show_thm "v_rel_subspt_typed=" clos_to_bvlProofTheory.v_rel_subspt;
val _ = show_thm "env_rel_subspt_typed=" clos_to_bvlProofTheory.env_rel_subspt;
val _ = show_thm "every_Fn_vs_NONE_known_co_typed=" clos_to_bvlProofTheory.every_Fn_vs_NONE_known_co;
val _ = show_thm "every_Fn_SOME_known_co_typed=" clos_to_bvlProofTheory.every_Fn_SOME_known_co;
val _ = show_thm "renumber_code_locs_list_csyntax_ok_typed=" clos_to_bvlProofTheory.renumber_code_locs_list_csyntax_ok;
val _ = show_thm "compile_every_Fn_vs_NONE_typed=" clos_to_bvlProofTheory.compile_every_Fn_vs_NONE;
val _ = show_thm "calls_compile_csyntax_ok_typed=" clos_to_bvlProofTheory.calls_compile_csyntax_ok;
val _ = show_thm "kcompile_inc_uncurry_typed=" clos_to_bvlProofTheory.kcompile_inc_uncurry;
val _ = show_thm "code_locs_FST_SND_kcompile_inc_typed=" clos_to_bvlProofTheory.code_locs_FST_SND_kcompile_inc;
val _ = show_thm "compile_code_locs_ALL_DISTINCT_typed=" clos_to_bvlProofTheory.compile_code_locs_ALL_DISTINCT;
val _ = show_thm "recclosure_rel_def_typed=" clos_callProofTheory.recclosure_rel_def;
val _ = show_thm "clos_call_wfv_def_typed=" clos_callProofTheory.wfv_def;
val _ = show_thm "clos_call_every_refv_def_typed=" clos_callProofTheory.every_refv_def;
val _ = show_thm "clos_call_every_refv_mono_typed=" clos_callProofTheory.every_refv_mono;
val _ = show_thm "clos_call_wfv_state_def_typed=" clos_callProofTheory.wfv_state_def;
val _ = show_thm "clos_call_wfv_subg_typed=" clos_callProofTheory.wfv_subg;
val _ = show_thm "clos_call_wfv_state_subg_typed=" clos_callProofTheory.wfv_state_subg;
val _ = show_thm "oracle_monotonic_init_subset_typed=" clos_to_bvlProofTheory.oracle_monotonic_init_subset;
val _ = show_thm "DISJOINT_LE_GT_typed=" clos_to_bvlProofTheory.DISJOINT_LE_GT;
val _ = show_thm "cond_mti_monotonic_elist_globals_typed=" clos_to_bvlProofTheory.cond_mti_monotonic_elist_globals;
val _ = show_thm "number_compile_inc_esgc_free_typed=" clos_to_bvlProofTheory.number_compile_inc_esgc_free;
val _ = show_thm "number_monotonic_elist_globals_typed=" clos_to_bvlProofTheory.number_monotonic_elist_globals;
val _ = show_thm "chain_exps_GT_typed=" clos_to_bvlProofTheory.chain_exps_GT;
val _ = show_thm "chain_exps_LE_typed=" clos_to_bvlProofTheory.chain_exps_LE;
val _ = show_thm "chain_exps_ALL_DISTINCT_typed=" clos_to_bvlProofTheory.chain_exps_ALL_DISTINCT;
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
