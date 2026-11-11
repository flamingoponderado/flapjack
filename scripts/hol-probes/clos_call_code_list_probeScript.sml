load "clos_callTheory"; load "clos_callProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = set_trace "Unicode" 0;
val _ = (print "code_list_type="; print_type (type_of ``clos_call$code_list``); print "\n");
val _ = (print "insert_each_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callTheory.insert_each_def); print "\n");
val _ = (print "fst_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.FST_code_list); print "\n");
val _ = (print "snd_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.SND_code_list_change); print "\n");
val _ = (print "map_fst_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.MAP_FST_code_list); print "\n");
val _ = (print "snd_zip_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.SND_code_list_ZIP); print "\n");
val _ = (print "alookup_code_list_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.ALOOKUP_code_list); print "\n");
val _ = (print "code_list_replace_snd_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.code_list_replace_SND); print "\n");
val _ = (print "calls_code_subset_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.calls_code_subset); print "\n");
val _ = (print "calls_domain_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.calls_domain); print "\n");
val _ = (print "calls_replace_snd_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.calls_replace_SND); print "\n");
val _ = (print "calls_acc_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.calls_acc); print "\n");
(* Replay the local accumulator theorem from its exported consequence. *)
val calls_acc_0_replay = prove
  (``!xs tmp x r. x ++ r = SND tmp ==>
      clos_call$calls xs tmp = (I ## I ## (combin$C (++) r)) (clos_call$calls xs (FST tmp,x))``,
   rpt gen_tac >> Cases_on `tmp` >> simp [] >> strip_tac >>
   qabbrev_tac `z = clos_call$calls xs (q,[])` >> PairCases_on `z` >>
   fs [] >>
   `clos_call$calls xs (q,x) = (z0,z1,z2 ++ x)` by
     (irule clos_callProofTheory.calls_acc >> simp []) >>
   `clos_call$calls xs (q,x ++ r) = (z0,z1,z2 ++ (x ++ r))` by
     (irule clos_callProofTheory.calls_acc >> simp []) >>
   fs [listTheory.APPEND_ASSOC] >> metis_tac []);
val _ = (print "calls_acc_0_replay_type="; Lib.with_flag (Globals.show_types,true) print_term (concl calls_acc_0_replay); print "\n");
(* Replay the local distinctness lemma with its original HOL proof. *)
val distinct_map_fst_add1_replay = prove
  (``!xs. ALL_DISTINCT (MAP (\k. FST k + 1n) xs) = ALL_DISTINCT (MAP FST xs)``,
   Induct >> fs [listTheory.MEM_MAP]);
val _ = (print "distinct_map_fst_add1_replay_type="; Lib.with_flag (Globals.show_types,true) print_term (concl distinct_map_fst_add1_replay); print "\n");
(* Replay the local existential congruence lemma with its original proof. *)
val imp_exists_iff_replay = prove
  (``!xs. (!x. MEM x xs ==> (P x <=> Q x)) ==> (EXISTS P xs <=> EXISTS Q xs)``,
   Induct >> fs []);
val _ = (print "imp_exists_iff_replay_type="; Lib.with_flag (Globals.show_types,true) print_term (concl imp_exists_iff_replay); print "\n");
val _ = (print "calls_el_sing_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.calls_el_sing); print "\n");
val _ = (print "v_rel_exists_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.v_rel_exists); print "\n");
val _ = (print "is_recclosure_def_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.is_Recclosure_def); print "\n");
val _ = (print "make_g_subg_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.make_g_subg); print "\n");
val _ = (print "make_g_make_g_eq_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.make_g_make_g_eq); print "\n");
val _ = (print "make_g_imp_subg_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.make_g_IMP_subg); print "\n");
val _ = (print "alookup_all_distinct_mem_type="; Lib.with_flag (Globals.show_types,true) print_term (concl alistTheory.ALOOKUP_ALL_DISTINCT_MEM); print "\n");
(* The source declaration is local, so replay its statement and original proof. *)
val code_includes_submap_replay = prove
  (``clos_callProof$code_includes x y1 /\ y1 SUBMAP y2 ==> clos_callProof$code_includes x y2``,
   fs [clos_callProofTheory.code_includes_def, finite_mapTheory.SUBMAP_DEF, finite_mapTheory.FLOOKUP_DEF] \\ metis_tac []);
val _ = (print "code_includes_submap_replay_type="; Lib.with_flag (Globals.show_types,true) print_term (concl code_includes_submap_replay); print "\n");
val _ = (print "dest_closure_v_rel_lookup_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.dest_closure_v_rel_lookup); print "\n");
val _ = (print "dest_closure_v_rel_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.dest_closure_v_rel); print "\n");
val _ = (print "dest_closure_partial_wfv_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.dest_closure_partial_wfv); print "\n");
val _ = (print "dest_closure_full_wfv_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.dest_closure_full_wfv); print "\n");
val _ = (print "insert_each_prime_def_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.insert_each'_def); print "\n");
val _ = (print "wfg_insert_each_prime_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.wfg_insert_each'); print "\n");
val _ = (print "fst_insert_each_prime_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.FST_insert_each'); print "\n");
val _ = (print "map_fst_insert_each_prime_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.MAP_FST_insert_each'); print "\n");
val _ = (print "snd_insert_each_prime_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.SND_insert_each'); print "\n");
val _ = (print "subg_insert_each_prime_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.subg_insert_each'); print "\n");
val _ = (print "fv_genlist_alt_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.fv_GENLIST_Var_alt); print "\n");
val _ = (print "env_exists_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.env_rel_env_exists); print "\n");
val _ = (print "evaluate_includes_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.evaluate_includes_state); print "\n");
val _ = (print "evaluate_app_includes_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.evaluate_app_includes_state); print "\n");
val _ = (print "evaluate_app_mono_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.evaluate_app_mono); print "\n");
val _ = (print "calls_pure_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.calls_pure); print "\n");
val _ = (print "calls_pure_sing_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.calls_pure_sing); print "\n");
val _ = (print "wfg_subg_refl_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.wfg_subg_refl); print "\n");
val _ = (print "wfg_subg_ex_helper_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.wfg_subg_EX_helper); print "\n");
val _ = (print "mk_code_g_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.mk_code_g_def); print "\n");
val _ = (print "pure_correct_eq_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.pure_correct_eq); print "\n");
open clos_callProofTheory finite_mapTheory;
(* The source theorem is local; replay its full statement and original proof. *)
val state_rel_refs_replay = prove
  (``(state_rel g l s1 s2 /\ FLOOKUP s1.refs n = r1 ==>
       ?r2. FLOOKUP s2.refs n = r2 /\ OPTREL (ref_rel (v_rel g l s2.code)) r1 r2) /\
     (state_rel g l s1 s2 /\ FLOOKUP s2.refs n = r2 ==>
       ?r1. FLOOKUP s1.refs n = r1 /\ OPTREL (ref_rel (v_rel g l s2.code)) r1 r2)``,
   rw [] \\ gvs [state_rel_def, FLOOKUP_DEF, fmap_rel_def] \\ rw []);
val _ = (print "state_rel_refs_replay_type="; Lib.with_flag (Globals.show_types,true) print_term (concl state_rel_refs_replay); print "\n");
val _ = (print "every_error_result_type="; Lib.with_flag (Globals.show_types,true) print_term (concl semanticPrimitivesPropsTheory.every_error_result_def); print "\n");
val _ = (print "every_result_type="; Lib.with_flag (Globals.show_types,true) print_term (concl semanticPrimitivesPropsTheory.every_result_def); print "\n");
val _ = (print "evaluate_add_clock_type="; Lib.with_flag (Globals.show_types,true) print_term (concl closPropsTheory.evaluate_add_clock); print "\n");
val _ = (print "evaluate_add_to_clock_type="; Lib.with_flag (Globals.show_types,true) print_term (concl closPropsTheory.evaluate_add_to_clock); print "\n");
val _ = (print "evaluate_mono_type="; Lib.with_flag (Globals.show_types,true) print_term (concl closPropsTheory.evaluate_mono); print "\n");
val _ = (print "disjoint_image_suc_type="; Lib.with_flag (Globals.show_types,true) print_term (concl miscTheory.DISJOINT_IMAGE_SUC); print "\n");
val _ = (print "image_suc_subset_union_type="; Lib.with_flag (Globals.show_types,true) print_term (concl miscTheory.IMAGE_SUC_SUBSET_UNION); print "\n");
val _ = (print "subspt_domain_subset_type="; Lib.with_flag (Globals.show_types,true) print_term (concl miscTheory.subspt_domain_SUBSET); print "\n");
val _ = (print "suffix_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.code_list_IS_SUFFIX); print "\n");
(* These local declarations are replayed with their original HOL proofs. *)
val code_locs_calls_list_replay = prove
  (``∀ls n tr i. closProps$code_locs (MAP SND (clos_call$calls_list tr i n ls)) = []``,
   Induct >> fs [clos_callTheory.calls_list_def, pairTheory.FORALL_PROD, Once closPropsTheory.code_locs_cons] >>
   rw [Once closPropsTheory.code_locs_def]);
val _ = (print "code_locs_calls_list_replay_type="; Lib.with_flag (Globals.show_types,true) print_term (concl code_locs_calls_list_replay); print "\n");
val code_locs_code_list_mem_replay = prove
  (``∀ls n rest x.
    MEM x (closProps$code_locs (MAP (SND o SND) (SND (clos_call$code_list n ls rest)))) ⇔
    MEM x (closProps$code_locs (MAP (SND o SND) (SND rest) ++ MAP SND ls))``,
   Induct >> fs [clos_callTheory.code_list_def, pairTheory.FORALL_PROD, Once closPropsTheory.code_locs_cons, closPropsTheory.code_locs_append] >>
   rw [] >> EVAL_TAC >> rw [EQ_IMP_THM] >> fs [Once closPropsTheory.code_locs_cons, closPropsTheory.code_locs_def]);
val _ = (print "code_locs_code_list_mem_replay_type="; Lib.with_flag (Globals.show_types,true) print_term (concl code_locs_code_list_mem_replay); print "\n");
val _ = (print "oracle_monotonic_init_union_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.oracle_monotonic_init_UNION); print "\n");
val _ = (print "fupdate_list_type="; Lib.with_flag (Globals.show_types,true) print_term (concl finite_mapTheory.FUPDATE_LIST); print "\n");
val _ = (print "semantics_calls_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.semantics_calls); print "\n");
val _ = (print "semantics_compile_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.semantics_compile); print "\n");
val _ = (print "nth_code_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.nth_code_def); print "\n");
val _ = (print "funion_fempty_fupdate_list_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.FUNION_FEMPTY_FUPDATE_LIST); print "\n");
val _ = (print "state_syntax_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.state_syntax_def); print "\n");
val _ = (print "state_syntax_insert_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.state_syntax_insert_each); print "\n");
val _ = (print "state_syntax_code_list_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.state_syntax_code_list); print "\n");
val _ = (print "calls_obeys_max_app_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.calls_obeys_max_app); print "\n");
val _ = (print "calls_no_labels_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.calls_no_Labels); print "\n");
val _ = (print "calls_correct_type="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.calls_correct); print "\n");
val entry = EVAL ``clos_call$code_list 10 [(2,closLang$Var None 4);(0,closLang$Var None 9);(1,closLang$Var None 2)] (sptree$LN,[(90,3,closLang$Var None 0)])``;
val _ = (print "example="; print_term (rhs (concl entry)); print "\n");
