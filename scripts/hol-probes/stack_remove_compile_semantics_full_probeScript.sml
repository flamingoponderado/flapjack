load "preamble";
load "helperLib";
open helperLib;
load "stack_removeProofTheory";
open HolKernel Parse bossLib preamble stack_removeProofTheory stack_removeTheory stackPropsTheory stackSemTheory stackLangTheory semanticsPropsTheory lprefix_lubTheory llistTheory;
val _ = Globals.linewidth := 20000;
(* comp_correct and state_rel_with_clock are original [local] theorems.
   Replay the existing complete literal comp_correct proof and its helpers. *)
val _ = QUse.use (OS.Path.concat
  (valOf (OS.Process.getEnv "FLAPJACK_HOL_PROBE_DIR"),
   "stack_remove_comp_correct_full_probeScript.sml"));
val comp_correct = cc_full;
val full_compile_semantics = GEN_ALL(prove(``
   state_rel jump off k s1 s2 /\ semantics start s1 <> Fail ==>
   semantics start s2 = semantics start s1``,
  simp[GSYM AND_IMP_INTRO] \\ strip_tac
  \\ simp[semantics_def]
  \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[]
  \\ DEEP_INTRO_TAC some_intro \\ full_simp_tac(srw_ss())[]
  \\ conj_tac
  >- (
    gen_tac >> ntac 2 strip_tac >>
    IF_CASES_TAC >> full_simp_tac(srw_ss())[] >- (
      first_x_assum(qspec_then`k''`mp_tac)>>simp[]>>
      (fn g => subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g) >>
      simp[] >>
      qmatch_assum_rename_tac`_ = (res,_)` >>
      Cases_on`res=SOME Error`>>simp[]>>
      old_drule comp_correct >>
      simp[reg_bound_def,RIGHT_FORALL_IMP_THM] >>
      old_drule (GEN_ALL state_rel_with_clock)
      \\ disch_then(qspec_then`k''`strip_assume_tac)
      \\ disch_then old_drule
      \\ simp[comp_def]
      \\ strip_tac \\ full_simp_tac(srw_ss())[]
      \\ qpat_x_assum`FST _ ≠ _`mp_tac
      \\ (fn g => subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g)
      \\ old_drule (GEN_ALL evaluate_add_clock)
      \\ full_simp_tac(srw_ss())[]
      \\ disch_then(qspec_then`ck`mp_tac)
      \\ simp[]) >>
    DEEP_INTRO_TAC some_intro >> full_simp_tac(srw_ss())[] >>
    conj_tac >- (
      srw_tac[][] >>
      Cases_on`r=TimeOut`>>full_simp_tac(srw_ss())[] >>
      qhdtm_x_assum`evaluate`mp_tac >>
      old_drule (GEN_ALL evaluate_add_clock) >>
      disch_then(qspec_then`k''`mp_tac) >>
      simp[] >> strip_tac >>
      old_drule comp_correct >>
      simp[RIGHT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
      impl_tac >- (
        rpt(first_x_assum(qspec_then`k'`mp_tac))>>srw_tac[][] ) >>
      simp[reg_bound_def,comp_def] >>
      old_drule (GEN_ALL state_rel_with_clock) >>
      disch_then(qspec_then`k'+k''`strip_assume_tac) >>
      disch_then old_drule >>
      strip_tac >> full_simp_tac(srw_ss())[] >>
      strip_tac >>
      qmatch_assum_abbrev_tac`evaluate (e,ss) = _` >>
      qspecl_then[`ck+k'`,`e`,`ss`]mp_tac(GEN_ALL evaluate_add_clock_io_events_mono)>>
      simp[Abbr`ss`] >> strip_tac >>
      old_drule (GEN_ALL evaluate_add_clock) >>
      disch_then(qspec_then`ck+k'`mp_tac) >>
      simp[] >> strip_tac >> fs[] >>
      first_x_assum(qspec_then`k''`mp_tac) >>
      simp[] >> strip_tac >> fs[state_rel_def]) >>
    old_drule comp_correct >>
    simp[RIGHT_FORALL_IMP_THM,GSYM AND_IMP_INTRO,reg_bound_def] >>
    impl_tac >- (
      rpt(first_x_assum(qspec_then`k'`mp_tac))>>srw_tac[][]) >>
    simp[comp_def] >>
    old_drule (GEN_ALL state_rel_with_clock)
    \\ disch_then(qspec_then`k'`strip_assume_tac)
    \\ disch_then old_drule
    \\ simp[] \\ strip_tac
    \\ first_x_assum(qspec_then`ck+k'`mp_tac)
    \\ simp[]
    \\ pop_assum mp_tac
    \\ BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[]
    \\ TRY (strip_tac \\ qexists_tac `ck + k'` \\ fs [])
    \\ first_x_assum(qspec_then`k'`mp_tac) \\ fs []
    \\ simp[] >> strip_tac >> full_simp_tac(srw_ss())[]
    \\ strip_tac \\ qexists_tac `ck + k'` \\ fs [])
  \\ strip_tac
  \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[]
  >- (
    full_simp_tac(srw_ss())[]
    \\ qpat_x_assum`_ ≠ _`mp_tac
    \\ (fn g => subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g)
    \\ strip_tac \\ full_simp_tac(srw_ss())[]
    \\ last_x_assum(qspec_then`k'`mp_tac)
    \\ (fn g => subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g)
    \\ old_drule comp_correct
    \\ qmatch_assum_rename_tac`_ = (res,_)`
    \\ Cases_on`res=SOME Error`\\ full_simp_tac(srw_ss())[]
    \\ old_drule (GEN_ALL state_rel_with_clock)
    \\ disch_then(qspec_then`k'`strip_assume_tac)
    \\ disch_then old_drule
    \\ simp[reg_bound_def,comp_def]
    \\ strip_tac
    \\ first_x_assum(qspec_then`k'`mp_tac)
    \\ simp[]
    \\ BasicProvers.FULL_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.FULL_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ ntac 2 (qhdtm_x_assum`evaluate`mp_tac)
    \\ old_drule (GEN_ALL evaluate_add_clock)
    \\ simp[] )
  \\ DEEP_INTRO_TAC some_intro \\ full_simp_tac(srw_ss())[]
  \\ conj_tac >- (
    srw_tac[][]
    \\ full_simp_tac(srw_ss())[METIS_PROVE[]``¬a ∨ b ⇔ a ⇒ b``]
    \\ full_simp_tac(srw_ss())[]
    \\ last_assum(qspec_then`k'`mp_tac)
    \\ (fn g => subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g)
    \\ qpat_x_assum`∀x y. _`(fn th => assume_tac th >> qspec_then`k'`mp_tac th)
    \\ simp[]
    \\ old_drule comp_correct
    \\ qmatch_assum_rename_tac`_ = (res,_)`
    \\ Cases_on`res=SOME Error`\\ full_simp_tac(srw_ss())[]
    \\ old_drule (GEN_ALL state_rel_with_clock)
    \\ disch_then(qspec_then`k'`strip_assume_tac)
    \\ disch_then old_drule
    \\ simp[reg_bound_def,comp_def]
    \\ strip_tac
    \\ qpat_x_assum`∀k. _ ∨ _`(fn th => assume_tac th >> qspec_then`ck+k'`mp_tac th)
    \\ qhdtm_x_assum`evaluate`mp_tac
    \\ simp_tac(srw_ss())[]
    \\ strip_tac
    \\ qpat_x_assum`option_CASE _ _ _`mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ strip_tac
    \\ `t2.ffi = r'.ffi`
    by (
      pop_assum mp_tac
      \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[state_rel_def] )
    \\ full_simp_tac(srw_ss())[]
    \\ qmatch_assum_abbrev_tac`evaluate (e,ss) = (_,t)`
    \\ qspecl_then[`e`,`ss`](mp_tac o Q.GEN`extra`) evaluate_add_clock_io_events_mono
    \\ disch_then(qspec_then`ck`mp_tac)
    \\ simp[Abbr`ss`] \\ strip_tac
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.FULL_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac evaluate_add_clock \\ rev_full_simp_tac(srw_ss())[]
    \\ first_x_assum(qspec_then`ck`mp_tac)
    \\ simp[])
  \\ simp[]
  \\ strip_tac
  \\ qmatch_abbrev_tac`build_lprefix_lub l1 = build_lprefix_lub l2`
  \\ `(lprefix_chain l1 ∧ lprefix_chain l2) ∧ equiv_lprefix_chain l1 l2`
       suffices_by metis_tac[build_lprefix_lub_thm,lprefix_lub_new_chain,unique_lprefix_lub]
  \\ conj_asm1_tac >- (
    UNABBREV_ALL_TAC >>
    conj_tac >>
    Ho_Rewrite.ONCE_REWRITE_TAC[GSYM o_DEF] >>
    REWRITE_TAC[IMAGE_COMPOSE] >>
    match_mp_tac prefix_chain_lprefix_chain >>
    simp[prefix_chain_def,PULL_EXISTS] >>
    qx_genl_tac[`k1`,`k2`] >>
    qspecl_then[`k1`,`k2`]mp_tac LESS_EQ_CASES >>
    metis_tac[
      LESS_EQ_EXISTS,
      evaluate_add_clock_io_events_mono
        |> CONV_RULE(SWAP_FORALL_CONV)
        |> Q.SPEC`s with <| use_alloc := F; clock := k; code := c|>`
        |> SIMP_RULE(srw_ss())[],
      evaluate_add_clock_io_events_mono
        |> CONV_RULE(SWAP_FORALL_CONV)
        |> Q.SPEC`s with <| clock := k |>`
        |> SIMP_RULE(srw_ss())[]]) >>
  simp[equiv_lprefix_chain_thm] >>
  unabbrev_all_tac >> simp[PULL_EXISTS] >>
  ntac 2 (pop_assum kall_tac) >>
  simp[LNTH_fromList,PULL_EXISTS] >>
  simp[GSYM FORALL_AND_THM] >>
  rpt gen_tac >>
  (fn g => subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g) >> full_simp_tac(srw_ss())[] >>
  (fn g => subterm (fn tm => Cases_on`^(assert (fn tm => has_pair_type tm andalso free_in tm (#2 g)) tm)`) (#2 g) g) >> full_simp_tac(srw_ss())[] >>
  old_drule comp_correct >>
  simp[comp_def,reg_bound_def,RIGHT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
  impl_tac >- (
    rpt(first_x_assum(qspec_then`k'`mp_tac))>>srw_tac[][] ) >>
  old_drule (GEN_ALL state_rel_with_clock) >>
  disch_then(qspec_then`k'`strip_assume_tac) >>
  disch_then old_drule >>
  strip_tac >> full_simp_tac(srw_ss())[] >>
  `t2.ffi = r'.ffi` by (
    pop_assum mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ TRY BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ simp[state_rel_def] ) >>
  reverse conj_tac >- (
    srw_tac[][] >>
    qexists_tac`ck+k'`>>simp[] ) >>
  srw_tac[][] >>
  qexists_tac`k'`>>simp[] >>
  ntac 2 (qhdtm_x_assum`evaluate`mp_tac) >>
  qmatch_assum_abbrev_tac`evaluate (e,ss) = _` >>
  qspecl_then[`ck`,`e`,`ss`]mp_tac(GEN_ALL evaluate_add_clock_io_events_mono)>>
  simp[Abbr`ss`] >>
  ntac 3 strip_tac >> full_simp_tac(srw_ss())[] >>
  rev_full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[IS_PREFIX_APPEND] >>
  simp[EL_APPEND1]));
val _ = if null(hyp full_compile_semantics) andalso null(free_vars(concl full_compile_semantics)) then () else raise Fail "open theorem";
val _ = print("compile_semantics_full_statement=" ^ term_to_string(concl full_compile_semantics) ^ "\n");
val _ = print("compile_semantics_full_proved=" ^ term_to_string(rhs(concl(EQT_INTRO full_compile_semantics))) ^ "\n");
