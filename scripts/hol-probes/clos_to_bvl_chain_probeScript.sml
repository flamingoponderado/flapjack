load "clos_to_bvlProofTheory";
load "preamble";
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
val _ = show_thm "alist_to_fmap_APPEND_typed=" alistTheory.alist_to_fmap_APPEND;
val _ = show_thm "lookup_fromList_typed=" sptreeTheory.lookup_fromList;
val _ = show_thm "lookup_fromAList_typed=" sptreeTheory.lookup_fromAList;
val _ = show_thm "fromAList_append_typed=" sptreeTheory.fromAList_append;
val _ = show_thm "init_code_ok_typed=" clos_to_bvlProofTheory.init_code_ok;
val _ = show_thm "clos_state_cc_def_typed=" clos_to_bvlProofTheory.clos_state_cc_def;
val _ = show_thm "kcompile_csyntax_ok_typed=" clos_to_bvlProofTheory.kcompile_csyntax_ok;
val _ = show_thm "elist_globals_SND_renumber_code_locs_list_typed=" clos_to_bvlProofTheory.elist_globals_SND_renumber_code_locs_list;
val _ = show_thm "elist_globals_SND_ncompile_inc_typed=" clos_to_bvlProofTheory.elist_globals_SND_ncompile_inc;
val _ = show_thm "compile_elist_globals_typed=" clos_to_bvlProofTheory.compile_elist_globals;
val _ = show_thm "mcompile_inc_uncurry_typed=" clos_to_bvlProofTheory.mcompile_inc_uncurry;
val _ = show_thm "acompile_inc_uncurry_typed=" clos_to_bvlProofTheory.acompile_inc_uncurry;
val _ = show_thm "ccompile_inc_uncurry_typed=" clos_to_bvlProofTheory.ccompile_inc_uncurry;
val _ = show_thm "compile_inc_uncurry_typed=" clos_to_bvlProofTheory.compile_inc_uncurry;
val _ = show_thm "fcompile_inc_uncurry_typed=" clos_to_bvlProofTheory.fcompile_inc_uncurry;
val _ = show_thm "semantics_cond_call_compile_inc_typed=" clos_to_bvlProofTheory.semantics_cond_call_compile_inc;
val _ = show_thm "compile_common_semantics_typed=" clos_to_bvlProofTheory.compile_common_semantics;
val _ = show_thm "compile_semantics_typed=" clos_to_bvlProofTheory.compile_semantics;
val _ = show_thm "BAG_UNION_MONO_typed=" clos_to_bvlProofTheory.BAG_UNION_MONO;
val _ = show_thm "BAG_FILTER_DEF_typed=" bagTheory.BAG_FILTER_DEF;
val _ = show_thm "FINITE_BAG_FILTER_typed=" bagTheory.FINITE_BAG_FILTER;
val _ = show_thm "BAG_IMAGE_DEF_typed=" bagTheory.BAG_IMAGE_DEF;
val _ = show_thm "BAG_CARD_RELn_typed=" bagTheory.BAG_CARD_RELn;
val _ = show_thm "BAG_CARD_typed=" bagTheory.BAG_CARD;
val _ = show_thm "FINITE_SUB_BAG_typed=" bagTheory.FINITE_SUB_BAG;
val _ = show_thm "SUB_BAG_CARD_typed=" bagTheory.SUB_BAG_CARD;
val _ = show_thm "BAG_IMAGE_SUB_BAG_typed=" clos_to_bvlProofTheory.BAG_IMAGE_SUB_BAG;
val _ = show_thm "trivia_1_typed=" clos_to_bvlProofTheory.trivia_1;
(* The source declaration is local; replay its original proof with inferred types. *)
val show_SUBSET_replay = Q.prove (
  `(!x. x IN s ==> x IN t) ==> s SUBSET t`,
  fs [pred_setTheory.SUBSET_DEF]);
val _ = show_thm "show_SUBSET_replay=" show_SUBSET_replay;
val _ = show_thm "EXISTS_CONS_NOT_NULL_typed=" clos_to_bvlProofTheory.EXISTS_CONS_NOT_NULL;
val _ = show_thm "code_locs_Op_cons_typed=" clos_to_bvlProofTheory.code_locs_Op_cons;
val _ = show_thm "compile_exps_IMP_acc_typed=" clos_to_bvlProofTheory.compile_exps_IMP_acc;
val _ = show_thm "build_aux_append_aux_typed=" clos_to_bvlProofTheory.build_aux_append_aux;
val _ = show_thm "compile_exps_append_aux_typed=" clos_to_bvlProofTheory.compile_exps_append_aux;
val _ = show_thm "compile_exps_eq_append_typed=" clos_to_bvlProofTheory.compile_exps_eq_append;
val _ = show_thm "SND_SND_known_compile_inc_typed=" clos_to_bvlProofTheory.SND_SND_known_compile_inc;
val _ = show_thm "alist_to_fmap_FEMPTY_typed=" clos_to_bvlProofTheory.alist_to_fmap_FEMPTY;
val _ = show_thm "code_locs_FST_ticks_compile_inc_typed=" clos_to_bvlProofTheory.code_locs_FST_ticks_compile_inc;
val _ = show_thm "code_locs_FST_letop_compile_inc_typed=" clos_to_bvlProofTheory.code_locs_FST_letop_compile_inc;
val _ = show_thm "ncompile_inc_code_locs_distinct_typed=" clos_to_bvlProofTheory.ncompile_inc_code_locs_distinct;
val _ = show_thm "every_Fn_vs_NONE_ncompile_inc_typed=" clos_to_bvlProofTheory.every_Fn_vs_NONE_ncompile_inc;
val _ = show_thm "every_Fn_SOME_ncompile_inc_typed=" clos_to_bvlProofTheory.every_Fn_SOME_ncompile_inc;
val _ = show_thm "set_code_locs_collect_apps_typed=" clos_to_bvlProofTheory.set_code_locs_collect_apps;
val _ = show_thm "every_Fn_SOME_collect_apps_typed=" clos_to_bvlProofTheory.every_Fn_SOME_collect_apps;
val _ = show_thm "every_Fn_SOME_intro_multi_typed=" clos_to_bvlProofTheory.every_Fn_SOME_intro_multi;
val _ = show_thm "HD_FST_calls_typed=" clos_to_bvlProofTheory.HD_FST_calls;
val _ = show_thm "elist_globals_sing_typed=" clos_to_bvlProofTheory.elist_globals_sing;
val _ = show_thm "set_globals_HD_intro_multi_typed=" clos_to_bvlProofTheory.set_globals_HD_intro_multi;
val _ = show_thm "set_globals_SND_renumber_code_locs_typed=" clos_to_bvlProofTheory.set_globals_SND_renumber_code_locs;
val _ = show_thm "elist_globals_FLAT_typed=" clos_to_bvlProofTheory.elist_globals_FLAT;
val _ = show_thm "eval_sim_def_typed=" clos_to_bvlProofTheory.eval_sim_def;
val _ = show_thm "IMP_semantics_eq_typed=" clos_to_bvlProofTheory.IMP_semantics_eq;
val _ = show_thm "clos_init_def_typed=" clos_to_bvlProofTheory.clos_init_def;
val _ = show_thm "clos_init_with_clock_typed=" clos_to_bvlProofTheory.clos_init_with_clock;
(* These local declarations are replayed with the proofs from the original script. *)
local
  open preamble clos_to_bvlTheory bvlSemTheory
  val evaluate_init1_replay = Q.prove (
    `∀mapp2 mapp1 tot st.
      (∀n. n < mapp2 ⇒ partial_app_fn_location mapp1 tot n ∈ domain st.code) ⇒
      bvlSem$evaluate (REVERSE
        (GENLIST (λprev. Op (Label (partial_app_fn_location mapp1 tot prev))[]) mapp2), [Unit], st) =
      (Rval (REVERSE (GENLIST (λprev. CodePtr (partial_app_fn_location mapp1 tot prev)) mapp2)), st)`,
    Induct >> fs[bvlSemTheory.evaluate_def] >>
    rw[] >> simp[GENLIST,REVERSE_SNOC] >>
    ONCE_REWRITE_TAC[CONS_APPEND] >>
    simp[bvlPropsTheory.evaluate_APPEND,bvlSemTheory.evaluate_def,do_app_def]);
  val evaluate_init_replay = Q.prove (
    `∀mapp2 mapp1 st.
      (∀m n. m < mapp2 ∧ n < m ⇒ partial_app_fn_location mapp1 m n ∈ domain st.code) ⇒
      bvlSem$evaluate (REVERSE (FLAT (GENLIST (λtot. GENLIST
        (λprev. Op (Label (partial_app_fn_location mapp1 tot prev))[]) tot) mapp2)), [Unit], st) =
      (Rval (REVERSE (FLAT (GENLIST (λtot. GENLIST
        (λprev. CodePtr (partial_app_fn_location mapp1 tot prev)) tot) mapp2))), st)`,
    Induct >> fs[bvlSemTheory.evaluate_def] >>
    simp[GENLIST,FLAT_SNOC] >>
    simp[REVERSE_APPEND,bvlPropsTheory.evaluate_APPEND] >>
    rw[] >>
    `∀n. n < mapp2 ⇒ partial_app_fn_location mapp1 mapp2 n ∈ domain st.code` by fs[] >>
    old_drule evaluate_init1_replay >> simp[]);
in
  val _ = show_thm "evaluate_init_replay=" evaluate_init_replay;
end;
val _ = show_thm "renumber_code_locs_fv1_typed=" clos_to_bvlProofTheory.renumber_code_locs_fv1;
val _ = show_thm "renumber_code_locs_list_fv_typed=" clos_to_bvlProofTheory.renumber_code_locs_list_fv;
val _ = show_thm "collect_apps_fv1_typed=" clos_to_bvlProofTheory.collect_apps_fv1;
val _ = show_thm "collect_args_fv1_typed=" clos_to_bvlProofTheory.collect_args_fv1;
val _ = show_thm "intro_multi_fv1_typed=" clos_to_bvlProofTheory.intro_multi_fv1;
val _ = show_thm "fv_append_typed=" closPropsTheory.fv_append;
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
val _ = show_thm "clos_call_wfv_SUBMAP_typed=" clos_callProofTheory.wfv_SUBMAP;
val _ = show_thm "clos_call_EVERY_wfv_SUBMAP_typed=" clos_callProofTheory.EVERY_wfv_SUBMAP;
val _ = show_thm "clos_call_EVERY_wfv_subg_typed=" clos_callProofTheory.EVERY_wfv_subg;
val _ = show_thm "clos_call_wfv_state_subg_typed=" clos_callProofTheory.wfv_state_subg;
val _ = show_thm "clos_call_wfv_state_SUBMAP_typed=" clos_callProofTheory.wfv_state_SUBMAP;
val _ = show_thm "clos_call_code_includes_subg_typed=" clos_callProofTheory.code_includes_subg;
val _ = show_thm "clos_call_code_includes_ALOOKUP_typed=" clos_callProofTheory.code_includes_ALOOKUP;
val _ = show_thm "clos_call_v_rel_def_typed=" clos_callProofTheory.v_rel_def;
val _ = show_thm "clos_call_v_rel_subg_typed=" clos_callProofTheory.v_rel_subg;
val _ = show_thm "clos_call_v_rel_SUBMAP_typed=" clos_callProofTheory.v_rel_SUBMAP;
val _ = show_thm "clos_call_v_rel_SUBMAP_subg_typed=" clos_callProofTheory.v_rel_SUBMAP_subg;
val _ = show_thm "clos_call_LIST_REL_v_rel_SUBMAP_typed=" clos_callProofTheory.LIST_REL_v_rel_SUBMAP;
val _ = show_thm "clos_call_LIST_REL_v_rel_subg_typed=" clos_callProofTheory.LIST_REL_v_rel_subg;
val _ = show_thm "clos_call_env_rel_SUBMAP_typed=" clos_callProofTheory.env_rel_SUBMAP;
val _ = show_thm "clos_call_env_rel_subg_typed=" clos_callProofTheory.env_rel_subg;
val _ = show_thm "clos_call_v_rel_Unit_typed=" clos_callProofTheory.v_rel_Unit;
val _ = show_thm "clos_call_v_to_list_thm_typed=" clos_callProofTheory.v_to_list_thm;
val _ = show_thm "clos_call_v_to_bytes_thm_typed=" clos_callProofTheory.v_to_bytes_thm;
val _ = show_thm "clos_call_v_to_words_thm_typed=" clos_callProofTheory.v_to_words_thm;
val _ = show_thm "clos_call_v_to_list_wfv_typed=" clos_callProofTheory.v_to_list_wfv;
val _ = show_thm "clos_call_wfv_Boolv_typed=" clos_callProofTheory.wfv_Boolv;
val _ = show_thm "clos_call_vrel_v2l_l2v_typed=" clos_callProofTheory.vrel_v2l_l2v;
val _ = show_thm "clos_call_wfv_v2l_l2v_typed=" clos_callProofTheory.wfv_v2l_l2v;
val _ = show_thm "clos_call_vrel_list_to_v_typed=" clos_callProofTheory.vrel_list_to_v;
val _ = show_thm "clos_call_wfv_v2l_typed=" clos_callProofTheory.wfv_v2l;
val _ = show_thm "clos_call_do_app_thm_typed=" clos_callProofTheory.do_app_thm;
val _ = show_thm "clos_call_domain_FST_insert_each_typed=" clos_callProofTheory.domain_FST_insert_each;
val _ = show_thm "clos_call_SND_insert_each_typed=" clos_callProofTheory.SND_insert_each;
val _ = show_thm "clos_call_FST_insert_each_same_typed=" clos_callProofTheory.FST_insert_each_same;
val _ = show_thm "clos_call_insert_each_pair_arg_typed=" clos_callProofTheory.insert_each_pair_arg;
val _ = show_thm "clos_call_insert_each_subspt_typed=" clos_callProofTheory.insert_each_subspt;
val _ = show_thm "clos_call_calls_subspt_typed=" clos_callProofTheory.calls_subspt;
val _ = show_thm "clos_call_calls_IS_SUFFIX_typed=" clos_callProofTheory.calls_IS_SUFFIX;
val _ = show_thm "clos_call_calls_subg_typed=" clos_callProofTheory.calls_subg;
val _ = show_thm "clos_call_calls_domain_locs_typed=" clos_callProofTheory.calls_domain_locs;
val _ = show_thm "clos_call_NOT_IN_domain_FST_g_typed=" clos_callProofTheory.NOT_IN_domain_FST_g;
val _ = show_thm "clos_call_wfg_insert_each_typed=" clos_callProofTheory.wfg'_insert_each;
val _ = show_thm "clos_call_v_rel_Boolv_typed=" clos_callProofTheory.v_rel_Boolv;
val _ = show_thm "clos_call_make_g_def_typed=" clos_callProofTheory.make_g_def;
val _ = show_thm "clos_call_make_g_wfg_typed=" clos_callProofTheory.make_g_wfg;
val _ = show_thm "clos_call_co_ok_def_typed=" clos_callProofTheory.co_ok_def;
val _ = show_thm "clos_call_co_ok_IMP_full_gs_eq_shift_seq_typed=" clos_callProofTheory.co_ok_IMP_full_gs_eq_shift_seq;
val _ = show_thm "clos_call_co_ok_IMP_wfg_full_gs_typed=" clos_callProofTheory.co_ok_IMP_wfg_full_gs;
val _ = show_thm "clos_call_co_ok_IMP_make_g_typed=" clos_callProofTheory.co_ok_IMP_make_g;
val _ = show_thm "clos_call_code_inv_def_typed=" clos_callProofTheory.code_inv_def;
val _ = show_thm "clos_call_code_inv_k_typed=" clos_callProofTheory.code_inv_k;
val _ = show_thm "clos_call_SUBMAP_FUPDATE_LIST_typed=" clos_callProofTheory.SUBMAP_FUPDATE_LIST;
val _ = show_thm "clos_call_includes_state_def_typed=" clos_callProofTheory.includes_state_def;
val _ = show_thm "clos_call_includes_state_EX_typed=" clos_callProofTheory.includes_state_EX;
(* This theorem is local in HOL; replay its statement and proof to retain inferred types. *)
val clos_call_env_rel_Op_Install_replay = Q.prove (
  `clos_callProof$env_rel r env env2 0 [(0, closLang$Op v6 closLang$Install e1)] <=>
   clos_callProof$env_rel r env env2 0 (MAP (λx. (0,x)) e1)`,
  fs [clos_callProofTheory.env_rel_def] >> rw [] >> fs [closPropsTheory.fv1_thm, listTheory.EXISTS_MAP]
  >> qsuff_tac `!x. EXISTS (λx'. closProps$fv1 x x') e1 = closProps$fv x e1` >> fs []
  >> Induct_on `e1` >> fs []);
val _ = show_thm "clos_call_env_rel_Op_Install_replay=" clos_call_env_rel_Op_Install_replay;
val _ = show_thm "clos_call_state_rel_def_typed=" clos_callProofTheory.state_rel_def;
val _ = show_thm "clos_call_state_rel_max_app_typed=" clos_callProofTheory.state_rel_max_app;
val _ = show_thm "clos_call_state_rel_clock_typed=" clos_callProofTheory.state_rel_clock;
val _ = show_thm "clos_call_state_rel_with_clock_typed=" clos_callProofTheory.state_rel_with_clock;
val _ = show_thm "clos_call_state_rel_flookup_refs_typed=" clos_callProofTheory.state_rel_flookup_refs;
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
