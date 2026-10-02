load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory reg_allocTheory reg_allocProofTheory linear_scanTheory linear_scanProofTheory wordLangTheory wordSemTheory wordPropsTheory wordConvsTheory word_allocTheory sptreeTheory;
val _ = Globals.linewidth := 1000;
val _ = temp_delsimps ["NORMEQ_CONV"]
val _ = diminish_srw_ss ["ABBREV"]
val _ = set_trace "BasicProvers.var_eq_old" 1

val _ = Parse.bring_to_front_overload"numset_list_insert"
             {Thy="word_alloc",Name="numset_list_insert"};
val _ = Parse.hide"mem";
val _ = temp_delsimps ["fromAList_def", "domain_union"]


val list_next_var_rename_lemma_1 = Q.prove (`  ∀ls ssa na ls' ssa' na'.
  list_next_var_rename ls ssa na = (ls',ssa',na') ⇒
  let len = LENGTH ls in
  ALL_DISTINCT ls' ∧
  ls' = (MAP (λx. 4*x+na) (COUNT_LIST len)) ∧
  na' = na + 4* len`,
  Induct>>
  full_simp_tac(srw_ss())[list_next_var_rename_def,LET_THM,next_var_rename_def,COUNT_LIST_def]>>
  ntac 7 strip_tac>>
  srw_tac[][]>>
  Cases_on`list_next_var_rename ls (insert h na ssa) (na+4)`>>
  Cases_on`r`>>full_simp_tac(srw_ss())[]>>
  res_tac
  >-
    (`∀x. MEM x q ⇒ na < x` by
      (srw_tac[][MEM_MAP]>>DECIDE_TAC)>>
    qpat_x_assum`A = ls'` (sym_sub_tac)>>
    `¬ MEM na q` by
      (SPOSE_NOT_THEN assume_tac>>
      res_tac>>DECIDE_TAC)>>
    full_simp_tac(srw_ss())[ALL_DISTINCT])
  >-
    (full_simp_tac(srw_ss())[MAP_MAP_o]>>
    qpat_x_assum`A = ls'` sym_sub_tac>>
    full_simp_tac(srw_ss())[MAP_EQ_f]>>srw_tac[][]>>
    DECIDE_TAC)
  >>
    DECIDE_TAC);
val ssa_map_ok_extend = Q.prove (`  ssa_map_ok na ssa ∧
  ¬is_phy_var na ⇒
  ssa_map_ok (na+4) (insert h na ssa)`,
  full_simp_tac(srw_ss())[ssa_map_ok_def]>>
  srw_tac[][]>>full_simp_tac(srw_ss())[lookup_insert]>>
  Cases_on`x=h`>>full_simp_tac(srw_ss())[]>>
  res_tac>-
    DECIDE_TAC);
val merge_moves_frame = Q.prove (`  ∀ls na ssaL ssaR.
  is_alloc_var na
  ⇒
  let(moveL,moveR,na',ssaL',ssaR') = merge_moves ls ssaL ssaR na in
  is_alloc_var na' ∧
  na ≤ na' ∧
  (ssa_map_ok na ssaL ⇒ ssa_map_ok na' ssaL') ∧
  (ssa_map_ok na ssaR ⇒ ssa_map_ok na' ssaR')`,
  Induct>>full_simp_tac(srw_ss())[merge_moves_def]>-
    (srw_tac[][]>>full_simp_tac(srw_ss())[])
  >>
  rpt strip_tac>>
  full_simp_tac(srw_ss())[LET_THM]>>
  last_x_assum(qspecl_then[`na`,`ssaL`,`ssaR`] assume_tac)>>
  rev_full_simp_tac(srw_ss())[]>>
  Cases_on`merge_moves ls ssaL ssaR na`>>PairCases_on`r`>>rev_full_simp_tac(srw_ss())[]>>
  EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
  (CONJ_TAC>-
    (full_simp_tac(srw_ss())[is_alloc_var_def]>>
    (assume_tac arithmeticTheory.MOD_PLUS>>full_simp_tac(srw_ss())[]>>
    pop_assum (qspecl_then [`4`,`r1`,`4`] assume_tac)>>
    rev_full_simp_tac(srw_ss())[]))
  >>
  CONJ_TAC>-
    DECIDE_TAC)
  >>
  metis_tac[ssa_map_ok_extend,convention_partitions]);
val fake_moves_frame = Q.prove (`  ∀ls na ssaL ssaR.
  is_alloc_var na
  ⇒
  let(moveL,moveR,na',ssaL',ssaR') = fake_moves prio ls ssaL ssaR na in
  is_alloc_var na' ∧
  na ≤ na' ∧
  (ssa_map_ok na ssaL ⇒ ssa_map_ok na' ssaL') ∧
  (ssa_map_ok na ssaR ⇒ ssa_map_ok na' ssaR')`,
  Induct>>full_simp_tac(srw_ss())[fake_moves_def]>-
    (srw_tac[][]>>full_simp_tac(srw_ss())[])
  >>
  rpt strip_tac>>
  full_simp_tac(srw_ss())[LET_THM]>>
  last_x_assum(qspecl_then[`na`,`ssaL`,`ssaR`] assume_tac)>>
  rev_full_simp_tac(srw_ss())[]>>
  Cases_on`fake_moves prio ls ssaL ssaR na`>>PairCases_on`r`>>rev_full_simp_tac(srw_ss())[]>>
  EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
  (CONJ_TAC>-
    (full_simp_tac(srw_ss())[is_alloc_var_def]>>
    (assume_tac arithmeticTheory.MOD_PLUS>>full_simp_tac(srw_ss())[]>>
    pop_assum (qspecl_then [`4`,`r1`,`4`] assume_tac)>>
    rev_full_simp_tac(srw_ss())[]))
  >>
  CONJ_TAC>-
    DECIDE_TAC)
  >>
  metis_tac[ssa_map_ok_extend,convention_partitions]);
val ssa_map_ok_more = Q.prove (`  ssa_map_ok na ssa ∧ na ≤ na' ⇒
  ssa_map_ok na' ssa`,
  full_simp_tac(srw_ss())[ssa_map_ok_def]>>srw_tac[][]
  >-
    metis_tac[]>>
  res_tac>>full_simp_tac(srw_ss())[]>>DECIDE_TAC);
val is_alloc_var_add = Q.prove (`  is_alloc_var na ⇒ is_alloc_var (na+4)`,
  full_simp_tac(srw_ss())[is_alloc_var_def]>>
  (qspec_then `4` assume_tac arithmeticTheory.MOD_PLUS>>full_simp_tac(srw_ss())[]>>
    pop_assum (qspecl_then [`na`,`4`] assume_tac)>>
    rev_full_simp_tac(srw_ss())[]));
val is_stack_var_add = Q.prove (`  is_stack_var na ⇒ is_stack_var (na+4)`,
  full_simp_tac(srw_ss())[is_stack_var_def]>>
  (qspec_then `4` assume_tac arithmeticTheory.MOD_PLUS>>full_simp_tac(srw_ss())[]>>
    pop_assum (qspecl_then [`na`,`4`] assume_tac)>>
    rev_full_simp_tac(srw_ss())[]));
val is_alloc_var_flip = Q.prove (`  is_alloc_var na ⇒ is_stack_var (na+2)`,
  full_simp_tac(srw_ss())[is_alloc_var_def,is_stack_var_def]>>
  ‘0 < 4:num’ by fs [] >>
  qspecl_then [`4`,`na`,`2`] assume_tac
    arithmeticTheory.MOD_PLUS >>
  full_simp_tac std_ss [EVAL “2 MOD 4”] >>
  strip_tac >> fs []);
val is_stack_var_flip = Q.prove (`  is_stack_var na ⇒ is_alloc_var (na+2)`,
  full_simp_tac(srw_ss())[is_alloc_var_def,is_stack_var_def]>>
  ‘0 < 4:num’ by fs [] >>
  qspecl_then [`4`,`na`,`2`] assume_tac
    arithmeticTheory.MOD_PLUS >>
  full_simp_tac std_ss [EVAL “2 MOD 4”] >>
  strip_tac >> fs []);
val list_next_var_rename_props = Q.prove (`  ∀ls ssa na ls' ssa' na'.
  list_next_var_rename ls ssa na = (ls',ssa',na') ==>
  (is_alloc_var na ∨ is_stack_var na) ∧
  ssa_map_ok na ssa
  ⇒
  na ≤ na' ∧
  (is_alloc_var na ⇒ is_alloc_var na') ∧
  (is_stack_var na ⇒ is_stack_var na') ∧
  ssa_map_ok na' ssa'`,
  Induct>>full_simp_tac(srw_ss())[list_next_var_rename_def,next_var_rename_def]>>
  LET_ELIM_TAC>>
  first_x_assum(qspecl_then[`ssa''`,`na''`,`ys`,`ssa'''`,`na'''`]
    mp_tac)>>
  (impl_tac>-simp[] >>
   impl_tac >-
    (full_simp_tac(srw_ss())[ssa_map_ok_def]>>srw_tac[][]
    >-
      metis_tac[is_alloc_var_add,is_stack_var_add]
    >-
      (full_simp_tac(srw_ss())[lookup_insert]>>Cases_on`x=h`>>full_simp_tac(srw_ss())[]>>
      metis_tac[convention_partitions])
    >-
      (full_simp_tac(srw_ss())[lookup_insert]>>Cases_on`x=h`>>full_simp_tac(srw_ss())[]>>
      res_tac>>DECIDE_TAC)))>>
  srw_tac[][]>> TRY(DECIDE_TAC)>> full_simp_tac(srw_ss())[]>>
  metis_tac[is_alloc_var_add,is_stack_var_add]);
val list_next_var_rename_move_props = Q.prove (`  ∀ls ssa na ls' ssa' na'.
  list_next_var_rename_move ssa na ls = (ls',ssa',na') ==>
  (is_alloc_var na ∨ is_stack_var na) ∧
  ssa_map_ok na ssa
  ⇒
  na ≤ na' ∧
  (is_alloc_var na ⇒ is_alloc_var na') ∧
  (is_stack_var na ⇒ is_stack_var na') ∧
  ssa_map_ok na' ssa'`,
  full_simp_tac(srw_ss())[list_next_var_rename_move_def]>>LET_ELIM_TAC>>
  full_simp_tac(srw_ss())[]>>
  imp_res_tac list_next_var_rename_props);
val ssa_cc_trans_inst_props = Q.prove (`  ∀i ssa na i' ssa' na'.
  ssa_cc_trans_inst i ssa na = (i',ssa',na') ==>
  ssa_map_ok na ssa ∧
  is_alloc_var na
  ⇒
  na ≤ na' ∧
  is_alloc_var na' ∧
  ssa_map_ok na' ssa'`,
  ho_match_mp_tac ssa_cc_trans_inst_ind>>rw[]>>
  gvs[ssa_cc_trans_inst_def,next_var_rename_def,AllCaseEqs()]>>
  rpt(pairarg_tac>>gvs[])>>
  `na + 8 = na + 4 +4` by fs[]>>
  metis_tac[is_alloc_var_add,ssa_map_ok_extend,convention_partitions]);
val fix_inconsistencies_props = Q.prove (`  ∀ssaL ssaR na a b na' ssaU.
  fix_inconsistencies prio ssaL ssaR na = (a,b,na',ssaU) ==>
  is_alloc_var na ∧
  ssa_map_ok na ssaL ∧
  ssa_map_ok na ssaR
  ⇒
  na ≤ na' ∧
  is_alloc_var na' ∧
  ssa_map_ok na' ssaU`,
  full_simp_tac(srw_ss())[fix_inconsistencies_def]>>LET_ELIM_TAC>>
  imp_res_tac merge_moves_frame>>
  pop_assum(qspecl_then[`ssaR`,`ssaL`,`var_union`] assume_tac)>>
  Q.ISPECL_THEN [`var_union`,`na''`,`ssa_L'`,`ssa_R'`] assume_tac fake_moves_frame>>
  rev_full_simp_tac(srw_ss())[LET_THM]>>
  DECIDE_TAC);
val ssa_map_ok_lem = Q.prove (`  ssa_map_ok na ssa ⇒ ssa_map_ok (na+2) ssa`,
  metis_tac[ssa_map_ok_more, DECIDE``na:num ≤ na+2``]);
val list_next_var_rename_move_props_2 = Q.prove (`  ∀ls ssa na ls' ssa' na'.
  list_next_var_rename_move ssa (na+2) ls = (ls',ssa',na') ==>
  (is_alloc_var na ∨ is_stack_var na) ∧ ssa_map_ok na ssa
  ⇒
  (na+2) ≤ na' ∧
  (is_alloc_var na ⇒ is_stack_var na') ∧
  (is_stack_var na ⇒ is_alloc_var na') ∧
  ssa_map_ok na' ssa'`,
  ntac 7 strip_tac>>imp_res_tac list_next_var_rename_move_props>>
  full_simp_tac(srw_ss())[]>>
  metis_tac[is_stack_var_flip,is_alloc_var_flip,ssa_map_ok_lem]);
val ssa_map_ok_inter = Q.prove (`  ssa_map_ok na ssa ⇒
  ssa_map_ok na (inter ssa ssa')`,
  full_simp_tac(srw_ss())[ssa_map_ok_def,lookup_inter]>>srw_tac[][]>>EVERY_CASE_TAC>>
  full_simp_tac(srw_ss())[]>>
  metis_tac[]);
val exp_tac = (LET_ELIM_TAC>>full_simp_tac(srw_ss())[next_var_rename_def]>>
    TRY(DECIDE_TAC)>>
    metis_tac[ssa_map_ok_extend,convention_partitions,is_alloc_var_add]);

val flip_rw = prove (``  is_stack_var(na+2) = is_alloc_var na ∧
    is_alloc_var(na+2) = is_stack_var na``,
  conj_tac >> (reverse EQ_TAC >-
    metis_tac[is_alloc_var_flip,is_stack_var_flip]) >>
  full_simp_tac(srw_ss())[is_alloc_var_def,is_stack_var_def]>>
  mp_tac arithmeticTheory.MOD_PLUS >>
  (disch_then(qspecl_then[`4`,`na`,`2`](SUBST1_TAC o SYM)) >>
  `na MOD 4 < 4` by full_simp_tac(srw_ss())[]>>
  imp_res_tac (DECIDE ``n:num<4⇒(n=0)∨(n=1)∨(n=2)∨(n=3)``)>>
  full_simp_tac(srw_ss())[]));

val th =
  (MATCH_MP
    (PROVE[]``((a ⇒ b) ∧ (c ⇒ d)) ⇒ ((a ∨ c) ⇒ b ∨ d)``)
    (CONJ is_stack_var_flip is_alloc_var_flip))

val swap_imp =PROVE[]``A ==> B ==> C <=> B ==> A ==> C``

val list_next_var_rename_props_2 =
  list_next_var_rename_props
  |> CONV_RULE(RESORT_FORALL_CONV(sort_vars["na","na'"]))
  |> Q.SPECL[`na+2`] |> SPEC_ALL
  |> UNDISCH
  |> REWRITE_RULE[GSYM AND_IMP_INTRO]
  |> C MATCH_MP (UNDISCH th)
  |> DISCH_ALL
  |> REWRITE_RULE[flip_rw]
  |> ONCE_REWRITE_RULE [swap_imp]
  |> UNDISCH
  |> REWRITE_RULE[AND_IMP_INTRO]
  |> DISCH_ALL
  |> GEN_ALL
  |> CONV_RULE(RESORT_FORALL_CONV(sort_vars["ls","ssa","na"]));


val ssa_cc_trans_props = Q.prove (`  ∀prog ssa na lt prog' ssa' na'.
  ssa_cc_trans prog ssa na lt = (prog',ssa',na') ==>
  ssa_map_ok na ssa ∧
  is_alloc_var na
  ⇒
  na ≤ na' ∧
  is_alloc_var na' ∧
  ssa_map_ok na' ssa'`,
  ho_match_mp_tac ssa_cc_trans_ind>>
  full_simp_tac(srw_ss())[ssa_cc_trans_def]>>
  rpt conj_tac >> rpt gen_tac
  >- (
    (* Move *)
    LET_ELIM_TAC>>
    full_simp_tac(srw_ss())[]
    >-
      metis_tac[list_next_var_rename_props]
    >-
      metis_tac[list_next_var_rename_props]
    >- (
      drule_at Any list_next_var_rename_props>>
      simp[]>>
      disch_then drule>>rw[]>>
      drule ssa_map_ok_force_rename>>
      disch_then match_mp_tac>>
      DEP_REWRITE_TAC[every_zip_snd]>>
      drule list_next_var_rename_lemma_1>>
      unabbrev_all_tac>>rw[EVERY_MEM,MEM_FILTER]>>
      pairarg_tac>>
      gvs[LENGTH_COUNT_LIST,MEM_MAP,MEM_COUNT_LIST,MEM_ZIP,EL_MAP,EL_COUNT_LIST]>>
      rename1`4 * xx + na`>>
      `is_alloc_var (4 * xx + na)` by
        gvs[is_alloc_var_def]>>
      metis_tac[convention_partitions]) )
  >- (
    (* StoreConsts *)
    LET_ELIM_TAC>>fs[next_var_rename_def]
    >- (
      rw[]>>
      `is_alloc_var ((d2+4)+4)` by
        fs[is_alloc_var_add]>>
      fs[])>>
    drule ssa_map_ok_extend >>
    disch_then(qspec_then `d` mp_tac)>>
    impl_tac >-
      metis_tac[convention_partitions]>>
    rw[]>>
    drule ssa_map_ok_extend >>
    disch_then(qspec_then `c` mp_tac)>>
    impl_tac >- metis_tac[convention_partitions,is_alloc_var_add]>>
    simp[])
  >-
    (LET_ELIM_TAC>>
    full_simp_tac(srw_ss())[]>>
    metis_tac[ssa_cc_trans_inst_props])
  >- exp_tac
  >- exp_tac
  >- exp_tac
  >-
    (LET_ELIM_TAC>>full_simp_tac(srw_ss())[]>>
    DECIDE_TAC)
  >-
    (LET_ELIM_TAC>>full_simp_tac(srw_ss())[]>>
    DECIDE_TAC)
  >-
    (LET_ELIM_TAC>>full_simp_tac(srw_ss())[]>>
    imp_res_tac ssa_map_ok_more>>
    first_x_assum(qspec_then`na3` assume_tac)>>rev_full_simp_tac(srw_ss())[]>>
    full_simp_tac(srw_ss())[]>>
    imp_res_tac fix_inconsistencies_props>>DECIDE_TAC)
  >-
    (* Alloc *)
    (full_simp_tac(srw_ss())[list_next_var_rename_move_def]>>LET_ELIM_TAC>>full_simp_tac(srw_ss())[]>>
    `∀naa. ssa_map_ok naa ssa''' ⇒ ssa_map_ok naa ssa_cut` by
      (srw_tac[][Abbr`ssa_cut`,ssa_map_ok_def,lookup_inter]>>
      EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
      metis_tac[])>>
    `na ≤ na+2 ∧ na'' ≤ na''+2` by DECIDE_TAC>>
    imp_res_tac ssa_map_ok_more>>
    imp_res_tac list_next_var_rename_props_2>>
    imp_res_tac ssa_map_ok_more>>
    res_tac>>
    imp_res_tac list_next_var_rename_props_2>>
    DECIDE_TAC)
  >- exp_tac
  >- exp_tac
  >- exp_tac
  >- exp_tac
  >- exp_tac
  >-
    (* Install *)
    (rpt gen_tac>> strip_tac>>
    simp[Once (GSYM markerTheory.Abbrev_def)]>>
    qpat_x_assum`_= (_,_,_)` mp_tac>>LET_ELIM_TAC >>
    ( (* multiple goals *)
      fs[next_var_rename_def]>>rw[]>>
      imp_res_tac list_next_var_rename_move_props_2>>
      rw[]>>fs[]>>
      rfs[]>>
      qabbrev_tac`na2 = na''+2`>>
      `is_alloc_var na2` by fs[Abbr`na2`,is_stack_var_flip]>>
      rw[]>>
      qmatch_asmsub_abbrev_tac`list_next_var_rename_move sss _ _ = _`>>
      Q.ISPECL_THEN[`ls`,`sss`,`na''+6`] mp_tac list_next_var_rename_move_props>>
      simp[]>>
      `is_alloc_var (na2+4)` by metis_tac[is_alloc_var_add]>>
      `na''+6 = na2+4` by fs[Abbr`na2`]>>
      impl_tac>-
        (simp[Abbr`sss`,Abbr`ssa_cut`]>>
        match_mp_tac ssa_map_ok_extend>>
        CONJ_TAC>-
         (match_mp_tac ssa_map_ok_inter>>
         fs[Abbr`na2`]>>
         match_mp_tac (GEN_ALL ssa_map_ok_more)>>
         asm_exists_tac>>fs[])>>
        metis_tac[convention_partitions])>>
      strip_tac>>
      fs[Abbr`na2`,markerTheory.Abbrev_def]))
  >- (* CBW *)
    (rw[]>>fs[])
  >- (* DBW *)
    (rw[]>>fs[])
  >-
    (full_simp_tac(srw_ss())[list_next_var_rename_move_def]>>LET_ELIM_TAC>>full_simp_tac(srw_ss())[]>>
    `∀naa. ssa_map_ok naa ssa''' ⇒ ssa_map_ok naa ssa_cut` by
      (srw_tac[][Abbr`ssa_cut`,ssa_map_ok_def,lookup_inter]>>
      EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
      metis_tac[])>>
    `na ≤ na+2 ∧ na'' ≤ na''+2` by DECIDE_TAC>>
    imp_res_tac ssa_map_ok_more>>
    imp_res_tac list_next_var_rename_props_2>>
    imp_res_tac ssa_map_ok_more>>
    res_tac>>
    imp_res_tac list_next_var_rename_props_2>>
    DECIDE_TAC)
  >-
    (LET_ELIM_TAC>>full_simp_tac(srw_ss())[]>>
    rev_full_simp_tac(srw_ss())[])
  >-
  (*Calls*)
  (Count.apply (Cases_on`h`>-
    (
    full_simp_tac(srw_ss())[]>> rpt (disch_tac ORELSE gen_tac)>>
    qpat_abbrev_tac `goal = (_ ∧ _ ∧ _)` >>
    ntac 3 (pop_assum mp_tac)>>LET_ELIM_TAC>>
    full_simp_tac(srw_ss())[PULL_FORALL,LET_THM]>>
    rveq >> gvs[] >>
    qspecl_then [`ret`, `ssa'''`, `na'''`]  assume_tac list_next_var_rename_props >>
    qspecl_then [`ls`, `ssa_cut`, `na''`]  assume_tac list_next_var_rename_move_props_2 >>
    qspecl_then [`ls`, `ssa`, `na`]  assume_tac list_next_var_rename_move_props_2 >>
    ntac 3 (pop_assum mp_tac) >>
    full_simp_tac(srw_ss())[] >>
    rpt strip_tac >>
    full_simp_tac(srw_ss())[] >>
    `ssa_map_ok na'' ssa_cut`
      by (
      pop_assum mp_tac >>
      srw_tac[][Abbr`ssa_cut`,ssa_map_ok_def,lookup_inter]>>
      EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
      metis_tac[]) >>
    full_simp_tac(srw_ss())[]>>
    full_simp_tac(srw_ss())[Abbr`goal`]>>
    intLib.ARITH_TAC)

  >>
    (*This is a slightly hacky mess*)
    PairCases_on`x`>>full_simp_tac(srw_ss())[list_next_var_rename_move_def]>>
    rpt (disch_tac ORELSE gen_tac)>>
    qpat_abbrev_tac `goal = (_ ∧ _ ∧ _)` >>
    ntac 3 (pop_assum mp_tac)>>LET_ELIM_TAC>>
    full_simp_tac(srw_ss())[PULL_FORALL,LET_THM]>>
    rveq >>
    full_simp_tac(srw_ss())[GSYM PULL_FORALL] >>
    rveq >>
    rev_full_simp_tac(srw_ss())[]>>
    drule_then assume_tac fix_inconsistencies_props >>
    qspecl_then [`ret`, `ssa''''`, `n''`]  (mp_tac) list_next_var_rename_props >>
    qspecl_then [`ls`, `ssa_cut`, `n'`]  (mp_tac) list_next_var_rename_props_2 >>
    qspecl_then [`ls`, `ssa`, `na`]  (mp_tac) list_next_var_rename_props_2 >>
    simp[] >>
    `∀naa. ssa_map_ok naa ssa'' ⇒ ssa_map_ok naa ssa_cut` by
      (srw_tac[][Abbr`ssa_cut`,ssa_map_ok_def,lookup_inter]>>
      full_simp_tac(srw_ss())[AllCaseEqs()]>>
      metis_tac[])>>
    `∀naa ssa. ssa_map_ok naa ssa ⇒ ssa_map_ok (naa + 2) ssa` by
      (
    rpt strip_tac >>
    irule ssa_map_ok_more>>
    first_x_assum (irule_at Any) >>
    intLib.ARITH_TAC) >>
    simp[] >>
    rpt $ disch_then strip_assume_tac >>
    Q.UNABBREV_TAC `goal` >>
    full_simp_tac(srw_ss())[next_var_rename_def] >>
    rveq >>
    qspecl_then [`ssa''''`, `n'''`,`x0`] mp_tac (GEN_ALL ssa_map_ok_extend) >>
    impl_tac >-(
        fs[Once convention_partitions] >>
        imp_res_tac ssa_map_ok_more>>metis_tac[]) >>
    rpt $ disch_then strip_assume_tac >>
    full_simp_tac(srw_ss())[is_alloc_var_add]>>
    rfs[] >>
    `ssa_map_ok na_3 ssa_2`
     by (irule ssa_map_ok_more >>
     qexists_tac `n'''` >>
     fs[]) >>
    fs[]))
  >- ((*ShareInst*)
    rpt gen_tac >>
    simp[LET_THM] >>
    IF_CASES_TAC
    >- (rw[] >> simp[]) >>
    pairarg_tac >>
    simp[] >>
    rpt $ disch_then strip_assume_tac >>
    gvs[next_var_rename_def] >>
    conj_tac >- fs[is_alloc_var_def] >>
    drule_then irule ssa_map_ok_extend >>
    metis_tac[convention_partitions] )
  >- ((*Loop*) (  strip_tac >>
  LET_ELIM_TAC >>
  fs[loop_setup_def] >>
  pairarg_tac >> fs[] >>
  pairarg_tac >> fs[] >>
  rveq >>
  drule_then assume_tac list_next_var_rename_props >>
  rfs[] >>
  qpat_x_assum `list_next_var_rename_move _ _ _ = _` assume_tac >>
  drule_then assume_tac list_next_var_rename_move_props >>
  rfs[] >>
  unabbrev_all_tac >>
  `ssa_map_ok na_refreshed (inter ssa_refreshed names)` by
    (match_mp_tac ssa_map_ok_inter >> first_x_assum ACCEPT_TAC) >>
  qpat_x_assum `_ ∧ is_alloc_var na_refreshed ⇒ _` mp_tac >>
  impl_tac >- simp[] >>
  strip_tac >>
  rpt conj_tac >>
  TRY (match_mp_tac ssa_map_ok_inter >>
       irule ssa_map_ok_more >>
       qexists_tac `na_refreshed`) >>
  gs[]))
  >- ((*Break*) (  fs[ssa_cc_trans_def]>>every_case_tac>>fs[]>>rveq>>simp[]))
  >- ((*Continue*) (  fs[ssa_cc_trans_def]>>every_case_tac>>fs[]>>rveq>>simp[])));
val ssa_reconcile_moves_eq = Q.prove (`  ∀L.
    FILTER (λ(a,b). a ≠ b)
      (FLAT (MAP (λv. case lookup v m of
                      | NONE => []
                      | SOME cv => [(f v, cv)]) L)) =
    MAP (λv. (f v, THE (lookup v m)))
      (FILTER (λv. case lookup v m of NONE => F | SOME cv => f v ≠ cv) L)`,
  Induct >> simp[] >>
  strip_tac >>
  Cases_on `lookup h m` >> fs[] >>
  IF_CASES_TAC >> simp[]);
val ssa_reconcile_filtered_all_distinct = Q.prove (`  ALL_DISTINCT (FILTER (λv. case lookup v cur_ssa of
                            | NONE => F
                            | SOME cv => option_lookup tgt_ssa v ≠ cv)
                  (MAP FST (toAList ns)))`,
  match_mp_tac FILTER_ALL_DISTINCT >>
  simp[ALL_DISTINCT_MAP_FST_toAList]);
val ssa_reconcile_get_vars_lemma = Q.prove (`  ∀ls cur_ssa (cst:('a,'b,'c) wordSem$state).
    ALL_DISTINCT ls ∧
    (∀v. MEM v ls ⇒
         ∃val. lookup (THE (lookup v cur_ssa)) cst.locals = SOME val) ⇒
    ∃vs. get_vars (MAP (λv. THE (lookup v cur_ssa)) ls) cst = SOME vs ∧
         LENGTH vs = LENGTH ls ∧
         ∀i. i < LENGTH ls ⇒
             lookup (THE (lookup (EL i ls) cur_ssa)) cst.locals = SOME (EL i vs)`,
  Induct >- simp[get_vars_def] >>
  rpt strip_tac >>
  fs[] >>
  `∃vs. get_vars (MAP (λv. THE (lookup v cur_ssa)) ls) cst = SOME vs ∧
        LENGTH vs = LENGTH ls ∧
        ∀i. i < LENGTH ls ⇒
            lookup (THE (lookup (EL i ls) cur_ssa)) cst.locals = SOME (EL i vs)`
    by (first_x_assum match_mp_tac >> rpt strip_tac >>
        last_x_assum match_mp_tac >> simp[]) >>
  `∃val. lookup (THE (lookup h cur_ssa)) cst.locals = SOME val`
    by (first_x_assum (qspec_then `h` mp_tac) >> simp[]) >>
  qexists_tac `val::vs` >>
  simp[get_vars_def, get_var_def] >>
  Cases >> simp[]);
val alookup_zip_map_some = Q.prove (`  ∀ls vs i f.
    ALL_DISTINCT (MAP f ls) ∧
    i < LENGTH ls ∧
    LENGTH vs = LENGTH ls ⇒
    ALOOKUP (ZIP (MAP f ls, vs)) (f (EL i ls)) = SOME (EL i vs)`,
  rpt strip_tac >>
  irule ALOOKUP_ALL_DISTINCT_MEM >>
  conj_tac
  >- (`LENGTH (MAP f ls) = LENGTH vs` by simp[LENGTH_MAP] >>
      simp[MAP_ZIP]) >>
  `LENGTH (MAP f ls) = LENGTH ls` by simp[LENGTH_MAP] >>
  simp[MEM_ZIP] >>
  qexists_tac `i` >> simp[EL_MAP]);
val alookup_zip_map_option_lookup_none = Q.prove (`  ∀ls vs n ns f.
    INJ f (domain ns) UNIV ∧
    n ∈ domain ns ∧
    ¬MEM n ls ∧
    (∀v. MEM v ls ⇒ v ∈ domain ns) ∧
    LENGTH vs = LENGTH ls ⇒
    ALOOKUP (ZIP (MAP f ls, vs)) (f n) = NONE`,
  rpt strip_tac >>
  Cases_on `ALOOKUP (ZIP (MAP f ls, vs)) (f n)` >> simp[] >>
  imp_res_tac ALOOKUP_MEM >>
  `LENGTH (MAP f ls) = LENGTH vs` by simp[LENGTH_MAP] >>
  fs[MEM_ZIP] >>
  `f n = f (EL n' ls)` by
    (`EL n' (MAP f ls) = f (EL n' ls)` by (irule EL_MAP >> simp[]) >>
     fs[]) >>
  `MEM (EL n' ls) ls` by (simp[MEM_EL] >> qexists_tac `n'` >> simp[]) >>
  `EL n' ls ∈ domain ns` by (first_x_assum irule >> simp[]) >>
  `EL n' ls = n` by (
    qpat_x_assum `INJ f _ _` mp_tac >>
    simp[INJ_DEF] >> strip_tac >>
    first_x_assum irule >> simp[]) >>
  fs[]);
val evaluate_ssa_reconcile = Q.prove (`  ssa_locals_rel na cur_ssa st_locs cst.locals ∧
  INJ (option_lookup tgt_ssa) (domain ns) UNIV ⇒
  ∃cst'.
    evaluate (ssa_reconcile cur_ssa tgt_ssa ns, cst) = (NONE, cst') ∧
    word_state_eq_rel cst cst' ∧
    strong_locals_rel (option_lookup tgt_ssa) (domain ns) st_locs cst'.locals`,
  rpt strip_tac >>
  simp[ssa_reconcile_def] >>
  qmatch_goalsub_abbrev_tac `if moves = [] then Skip else _` >>
  `moves = MAP (λv. (option_lookup tgt_ssa v, THE (lookup v cur_ssa)))
    (FILTER (λv. case lookup v cur_ssa of
                 | NONE => F
                 | SOME cv => option_lookup tgt_ssa v ≠ cv)
       (MAP FST (toAList ns)))` by
    (unabbrev_all_tac >> simp[ssa_reconcile_moves_eq]) >>
  qmatch_asmsub_abbrev_tac `MAP _ filtered_vars` >>
  `ALL_DISTINCT filtered_vars` by
    (unabbrev_all_tac >> simp[ssa_reconcile_filtered_all_distinct]) >>
  `∀v. MEM v filtered_vars ⇒ v ∈ domain ns ∧
       ∃cv. lookup v cur_ssa = SOME cv ∧ option_lookup tgt_ssa v ≠ cv ∧
            THE (lookup v cur_ssa) = cv` by
    (unabbrev_all_tac >>
     simp[MEM_FILTER, MEM_MAP, MEM_toAList, PULL_EXISTS, EXISTS_PROD] >>
     rpt strip_tac >>
     Cases_on `lookup v cur_ssa` >> fs[domain_lookup]) >>
  `ALL_DISTINCT (MAP (option_lookup tgt_ssa) filtered_vars)` by
    (match_mp_tac ALL_DISTINCT_MAP_INJ >>
     conj_tac >- (rw[] >> res_tac >> fs[INJ_DEF]) >>
     simp[]) >>
  Cases_on `moves = []`
  >- (
  simp[evaluate_def, word_state_eq_rel_def, strong_locals_rel_def] >>
  rpt strip_tac >>
  `n ∈ domain cur_ssa ∧ lookup (THE (lookup n cur_ssa)) cst.locals = SOME v`
    by (fs[ssa_locals_rel_def] >> res_tac >> simp[]) >>
  Cases_on `lookup n cur_ssa` >- fs[domain_lookup] >>
  rename1 `lookup n cur_ssa = SOME cv` >>
  `lookup cv cst.locals = SOME v` by fs[] >>
  `filtered_vars = []` by (Cases_on `filtered_vars` >> fs[]) >>
  `option_lookup tgt_ssa n = cv` by (
    qpat_x_assum `filtered_vars = _` mp_tac >>
    unabbrev_all_tac >>
    simp[FILTER_EQ_NIL, EVERY_MEM, MEM_MAP, MEM_toAList, EXISTS_PROD,
         PULL_EXISTS] >>
    fs[domain_lookup] >>
    disch_then drule >>
    simp[]) >>
  simp[]
)
  >- (
  simp[evaluate_def] >>
  `MAP FST moves = MAP (option_lookup tgt_ssa) filtered_vars ∧
   MAP SND moves = MAP (λv. THE (lookup v cur_ssa)) filtered_vars` by
    (qpat_x_assum `moves = MAP _ _` SUBST1_TAC >>
     simp[MAP_MAP_o, combinTheory.o_DEF] >>
     simp[MAP_EQ_f]) >>
  simp[] >>
  `∀v. MEM v filtered_vars ⇒
       ∃val. lookup (THE (lookup v cur_ssa)) cst.locals = SOME val` by (
    rpt strip_tac >> res_tac >>
    fs[ssa_locals_rel_def] >>
    res_tac >> fs[domain_lookup]) >>
  `∃vs. get_vars (MAP (λv. THE (lookup v cur_ssa)) filtered_vars) cst
          = SOME vs ∧
        LENGTH vs = LENGTH filtered_vars ∧
        ∀i. i < LENGTH filtered_vars ⇒
            lookup (THE (lookup (EL i filtered_vars) cur_ssa)) cst.locals =
              SOME (EL i vs)`
    by (match_mp_tac ssa_reconcile_get_vars_lemma >> simp[]) >>
  qexists_tac
    `cst with locals := alist_insert
       (MAP (option_lookup tgt_ssa) filtered_vars) vs cst.locals` >>
  simp[set_vars_def, MAP_MAP_o, combinTheory.o_DEF, GSYM (SF ETA_ss)] >>
  simp[word_state_eq_rel_def, strong_locals_rel_def] >>
  rpt strip_tac >>
  `n ∈ domain cur_ssa ∧ lookup (THE (lookup n cur_ssa)) cst.locals = SOME v`
    by (fs[ssa_locals_rel_def] >> res_tac >> simp[]) >>
  Cases_on `lookup n cur_ssa` >- fs[domain_lookup] >>
  rename1 `lookup n cur_ssa = SOME cv` >>
  `lookup cv cst.locals = SOME v` by fs[] >>
  simp[lookup_alist_insert] >>
  Cases_on `option_lookup tgt_ssa n = cv`
  >- (
    (* Case A: not in filtered_vars *)
    `¬MEM n filtered_vars` by (
      strip_tac >> res_tac >> fs[]) >>
    `ALOOKUP (ZIP (MAP (option_lookup tgt_ssa) filtered_vars, vs))
       (option_lookup tgt_ssa n) = NONE` by (
      qspecl_then [`filtered_vars`, `vs`, `n`, `ns`, `option_lookup tgt_ssa`]
        mp_tac alookup_zip_map_option_lookup_none >>
      impl_tac
      >- (simp[] >> rpt strip_tac >> res_tac >> simp[]) >>
      simp[]) >>
    fs[]) >>
  (* Case B: in filtered_vars *)
  `MEM n filtered_vars` by (
    unabbrev_all_tac >>
    simp[MEM_FILTER, MEM_MAP, MEM_toAList, EXISTS_PROD] >>
    fs[domain_lookup] >> metis_tac[]) >>
  `∃i. i < LENGTH filtered_vars ∧ EL i filtered_vars = n` by metis_tac[MEM_EL] >>
  `ALOOKUP (ZIP (MAP (option_lookup tgt_ssa) filtered_vars, vs))
     (option_lookup tgt_ssa n) = SOME (EL i vs)` by (
    qpat_x_assum `EL i filtered_vars = n` (assume_tac o GSYM) >>
    simp[] >>
    irule alookup_zip_map_some >>
    simp[]) >>
  simp[] >>
  first_x_assum (qspec_then `i` mp_tac) >>
  impl_tac >- simp[] >>
  simp[] >> rw[]
));
val cut_env_fromAList_LN = Q.prove (`  cut_env (a, fromAList (MAP (g:num#unit -> num#unit) (toAList LN))) v =
  cut_env (a, LN) v`,
  simp[cut_env_def, cut_envs_def, cut_names_def,
       sptreeTheory.toAList_def, sptreeTheory.foldi_def,
       sptreeTheory.fromAList_def] >>
  rpt CASE_TAC >> simp[]);
val ssa_cc_trans_Loop_helper = Q.prove (`  ∀(st:('a,'b,'c) wordSem$state) cst ssa_refreshed na_refreshed
    names body exit_names lt body' ssa' na'.
    word_state_eq_rel st cst ∧
    strong_locals_rel (option_lookup ssa_refreshed) (domain names)
      st.locals cst.locals ∧
    (∀v. v ∈ domain names ⇒
       option_lookup ssa_refreshed v ∈ domain cst.locals) ∧
    ssa_map_ok na_refreshed ssa_refreshed ∧
    is_alloc_var na_refreshed ∧
    every_var (λx. x < na_refreshed) body ∧
    INJ (option_lookup ssa_refreshed) (domain names) UNIV ∧
    INJ (option_lookup ssa_refreshed) (domain exit_names) UNIV ∧
    domain names ⊆ domain ssa_refreshed ∧
    domain exit_names ⊆ domain ssa_refreshed ∧
    EVERY (λx. x < na_refreshed) (MAP FST (toAList names)) ∧
    EVERY (λx. x < na_refreshed) (MAP FST (toAList exit_names)) ∧
    lt_ok lt ∧
    ssa_cc_trans body (inter ssa_refreshed names) na_refreshed
      ((ssa_refreshed,names,exit_names)::lt) = (body',ssa',na') ∧
    (∀(st':('a,'b,'c) wordSem$state) cst' ssa'' na'' lt'.
       word_state_eq_rel st' cst' ∧
       ssa_locals_rel na'' ssa'' st'.locals cst'.locals ∧
       is_alloc_var na'' ∧
       every_var (λx. x < na'') body ∧
       ssa_map_ok na'' ssa'' ∧
       lt_ok lt' ⇒
       ∃perm'.
         (let (res,rst) = evaluate (body, st' with permute := perm') in
            res = SOME Error ∨
            (let (prog',ssaB,naB) = ssa_cc_trans body ssa'' na'' lt';
                 (res',rcst) = evaluate (prog', cst') in
               res = res' ∧ word_state_eq_rel rst rcst ∧
               case res of
                 NONE => ssa_locals_rel naB ssaB rst.locals rcst.locals
               | SOME (Break n) =>
                   (case oEL n lt' of
                      NONE => T
                    | SOME (tgt_ssa,_,exit_names) =>
                        strong_locals_rel (option_lookup tgt_ssa)
                          (domain exit_names) rst.locals rcst.locals)
               | SOME (Continue n') =>
                   (case oEL n' lt' of
                      NONE => T
                    | SOME (tgt_ssa,names,_) =>
                        strong_locals_rel (option_lookup tgt_ssa)
                          (domain names) rst.locals rcst.locals)
               | SOME _ => rst.locals = rcst.locals))) ⇒
    let back_moves = ssa_reconcile ssa' ssa_refreshed names in
    let body_final = if back_moves = Skip then body' else Seq body' back_moves in
    let ssa_names = apply_nummap_key (option_lookup ssa_refreshed) names in
    let ssa_exit = apply_nummap_key (option_lookup ssa_refreshed) exit_names in
    ∀res' rcst.
      evaluate (Loop ssa_names body_final ssa_exit, cst) = (res',rcst) ⇒
      ∃perm'.
        (λ(res,rst).
            res = SOME Error ∨
            res = res' ∧ word_state_eq_rel rst rcst ∧
            case res of
              NONE => ssa_locals_rel na' (inter ssa_refreshed exit_names)
                        rst.locals rcst.locals
            | SOME (Break n) =>
                (case oEL n lt of
                   NONE => T
                 | SOME (tgt_ssa,_,exit_names) =>
                     strong_locals_rel (option_lookup tgt_ssa)
                       (domain exit_names) rst.locals rcst.locals)
            | SOME (Continue n') =>
                (case oEL n' lt of
                   NONE => T
                 | SOME (tgt_ssa,names,_) =>
                     strong_locals_rel (option_lookup tgt_ssa)
                       (domain names) rst.locals rcst.locals)
            | SOME _ => rst.locals = rcst.locals)
          (evaluate (Loop names body exit_names, st with permute := perm'))`,
  gen_tac>>
  qid_spec_tac `st`>>
  completeInduct_on `cst.clock`>>
  rpt strip_tac>>
  simp[LET_DEF]>>
  rpt gen_tac>>strip_tac>>
  qpat_x_assum `evaluate (Loop _ _ _, cst) = _` mp_tac>>
  simp[Once evaluate_def]>>
  TOP_CASE_TAC>>fs[]
  >- ((* target_cut_none *)
      strip_tac >>
      qpat_x_assum `cut_state _ cst = NONE` mp_tac >>
      simp[cut_state_def, cut_env_def, cut_envs_def, cut_names_def,
           apply_nummap_key_def, domain_fromAList, MAP_MAP_o,
           combinTheory.o_DEF, SUBSET_DEF, MEM_MAP, EXISTS_PROD,
           MEM_toAList, AllCaseEqs(), PULL_EXISTS] >>
      rpt strip_tac >>
      fs[SUBSET_DEF, domain_lookup] >>
      metis_tac[]) >>
  (* main: source cut split *)
  rename1 `cut_state _ cst = SOME cut_cst` >>
  strip_tac >>
  Cases_on `cut_state (names,LN) st`
  >- (qexists_tac `cst.permute` >>
      simp[Once evaluate_def]) >>
  rename1 `cut_state (names,LN) st = SOME cut_st` >>
  (* core: drive cut_env_lemma *)
  simp[Once evaluate_def] >>
  fs[cut_state_def, AllCaseEqs()] >>
  drule_at (Pos (el 2)) cut_env_lemma >>
  disch_then (qspecl_then [`cst.locals`, `option_lookup ssa_refreshed`] mp_tac) >>
  impl_tac
  >- (simp[domain_union] >>
      fs[strong_locals_rel_def, apply_nummap_key_def] >>
      rw[]) >>
  strip_tac >>
  (* after_cut_lemma *)
  gvs[apply_nummaps_key_def, cut_env_fromAList_LN] >>
  (* after_cut_unified: instantiate body-IH *)
  last_assum (qspecl_then
    [`st with locals := env'`,
     `cst with locals := env`,
     `inter ssa_refreshed names`,
     `na_refreshed`,
     `(ssa_refreshed,names,exit_names)::lt`] mp_tac) >>
  impl_tac
  >- (rpt conj_tac
      >- fs[word_state_eq_rel_def]
      >- ((* body_ih_locals_rel: 5-conjunct ssa_locals_rel *)
          simp[ssa_locals_rel_def] >>
          rw[]
          >- ((* blr_case_inter_dom *)
              rename1 `lookup k1 (inter _ _) = SOME _` >>
              qexists_tac `k1` >>
              Cases_on `lookup k1 names` >>
              gvs[sptreeTheory.lookup_inter_EQ, option_lookup_def,
                  sptreeTheory.domain_lookup])
          >- ((* blr_case_dom_ssa *)
              `x ∈ domain env'` by
                (simp[sptreeTheory.domain_lookup] >> metis_tac[]) >>
              `x ∈ domain names` by metis_tac[] >>
              fs[SUBSET_DEF])
          >- ((* blr_case_dom_names *)
              `x ∈ domain env'` by
                (simp[sptreeTheory.domain_lookup] >> metis_tac[]) >>
              metis_tac[])
          >- ((* blr_case_lookup_env *)
              subgoal `x ∈ domain env'`
              >- (simp[sptreeTheory.domain_lookup] >> metis_tac[]) >>
              subgoal `x ∈ domain names` >- metis_tac[] >>
              subgoal `x ∈ domain ssa_refreshed`
              >- metis_tac[SUBSET_DEF] >>
              Cases_on `lookup x ssa_refreshed`
              >- fs[sptreeTheory.domain_lookup] >>
              gvs[sptreeTheory.lookup_inter_alt] >>
              qpat_x_assum
                `strong_locals_rel _ _ env' env`
                (mp_tac o REWRITE_RULE [strong_locals_rel_def]) >>
              disch_then (qspecl_then [`x`, `y`] mp_tac) >>
              simp[option_lookup_def])
          >- ((* blr_case_alloc *)
              `x ∈ domain env'` by
                (simp[sptreeTheory.domain_lookup] >> metis_tac[]) >>
              `x ∈ domain names` by metis_tac[] >>
              fs[EVERY_MEM, toAList_domain]))
      >- fs[]
      >- fs[every_var_def]
      >- ((* body_ih_map_ok *)
          fs[ssa_map_ok_def, sptreeTheory.lookup_inter_EQ] >>
          metis_tac[])
      >- (fs[lt_ok_def] >>
          first_assum ACCEPT_TAC)) >>
  strip_tac >>
  Cases_on `evaluate (body,st with <|permute := perm'; locals := env'|>)` >>
  rename1 `evaluate (body, _) = (bres, brst)` >>
  Cases_on `bres = SOME Error`
  >- (qexists_tac `perm'` >>
      simp[Once wordSemTheory.evaluate_def] >>
      `cut_state (names,LN) st = SOME (st with locals := env')` by
        fs[wordSemTheory.cut_state_def] >>
      gvs[wordSemTheory.exit_loop_def, wordSemTheory.cont_loop_def]) >>
  fs[] >>
  Cases_on `evaluate (body',cst with locals := env)` >>
  rename1 `evaluate (body', _) = (bres', brcst)` >>
  fs[] >>
  Cases_on `bres`
  >- ((* NONE: cont_loop fires; recurse via clock-IH *)
      (
  qpat_x_assum `_ (ssa_cc_trans body _ _ _)` mp_tac >>
  simp[LLOOKUP_def] >>
  strip_tac >>
  (* Run evaluate_ssa_reconcile to bridge from ssa_locals_rel (body-IH NONE
     conclusion) to strong_locals_rel.  In Skip case the post-state cst'
     coincides with brcst (since evaluate(Skip, brcst) = (NONE, brcst));
     in non-Skip case cst' is the post-ssa_reconcile state. *)
  mp_tac (let val tvs = type_vars_in_term (Thm.concl evaluate_ssa_reconcile)
              val delta = List.hd tvs
              val typed = INST_TYPE [delta |-> Type`:unit`] evaluate_ssa_reconcile
          in Q.SPECL [`ssa_refreshed`, `brst.locals`, `names`,
                      `na'`, `ssa'`, `brcst`] (GEN_ALL typed) end) >>
  impl_tac
  >- (conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  Cases_on `brst.clock = 0`
  >- ((* TimeOut case *)
      qexists_tac `perm'` >>
      simp[Once wordSemTheory.evaluate_def] >>
      `cut_state (names,LN) st = SOME (st with locals := env')` by
        fs[wordSemTheory.cut_state_def] >>
      simp[] >>
      gvs[] >>
      Cases_on `ssa_reconcile ssa' ssa_refreshed names = Skip` >>
      gvs[wordSemTheory.evaluate_def, wordSemTheory.cont_loop_def]
      >- (`brcst.clock = 0` by fs[word_state_eq_rel_def] >>
          gvs[wordSemTheory.flush_state_def, word_state_eq_rel_def]) >>
      `cst'.clock = 0` by fs[word_state_eq_rel_def] >>
      gvs[wordSemTheory.flush_state_def, word_state_eq_rel_def]) >>
  (* clock != 0: source recursive Loop on dec_clock brst, target on dec_clock cst' *)
  `brst.clock = brcst.clock` by fs[word_state_eq_rel_def] >>
  `brcst.clock = cst'.clock` by fs[word_state_eq_rel_def] >>
  Cases_on `cut_env (names, LN) brst.locals`
  >- ((* source recursive cut fails: source returns Error *)
      qexists_tac `perm'` >>
      simp[Once wordSemTheory.evaluate_def] >>
      `cut_state (names,LN) (st with permute := perm') =
         SOME (st with <|permute := perm'; locals := env'|>)` by
        fs[wordSemTheory.cut_state_def] >>
      simp[] >>
      `(brst with clock := brst.clock).clock ≠ 0` by simp[] >>
      gvs[wordSemTheory.fix_clock_def, wordSemTheory.cont_loop_def,
          STOP_def, wordSemTheory.dec_clock_def] >>
      simp[Once wordSemTheory.evaluate_def,
           wordSemTheory.cut_state_def]) >>
  imp_res_tac wordSemTheory.evaluate_clock >>
  `(dec_clock cst').clock < cst.clock` by gvs[dec_clock_def] >>
  qpat_x_assum `∀m. m < cst.clock ⇒ _`
    (qspec_then `(dec_clock cst').clock` mp_tac) >>
  impl_keep_tac >- simp[] >>
  disch_then (qspec_then `dec_clock cst'` mp_tac) >>
  simp[] >>
  `domain names ⊆ domain brst.locals` by
    (qpat_x_assum `cut_env (names,LN) brst.locals = _`
       (mp_tac o REWRITE_RULE [wordSemTheory.cut_env_def]) >>
     simp[AllCaseEqs()] >>
     rpt strip_tac >>
     drule cut_envs_domain_SUBSET >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `∀v. v ∈ domain names ⇒
         option_lookup ssa_refreshed v ∈ domain cst'.locals` by
    (rpt strip_tac >>
     `∃v''. lookup v brst.locals = SOME v''` by
       (`v ∈ domain brst.locals` by
          (qpat_x_assum `domain names ⊆ domain brst.locals` mp_tac >>
           simp[SUBSET_DEF] >> disch_then drule >> simp[]) >>
        qpat_x_assum `v ∈ domain brst.locals` mp_tac >>
        simp[domain_lookup]) >>
     `lookup (option_lookup ssa_refreshed v) cst'.locals = SOME v''` by
       (qpat_x_assum `strong_locals_rel _ _ brst.locals cst'.locals`
          (mp_tac o REWRITE_RULE [strong_locals_rel_def]) >>
        disch_then (qspecl_then [`v`, `v''`] mp_tac) >>
        impl_tac
        >- (conj_tac
            >- first_assum ACCEPT_TAC
            >- first_assum ACCEPT_TAC) >>
        strip_tac >> first_assum ACCEPT_TAC) >>
     simp[domain_lookup] >>
     qexists_tac `v''` >>
     first_assum ACCEPT_TAC) >>
  disch_then (qspecl_then
    [`dec_clock brst`, `ssa_refreshed`, `na_refreshed`,
     `names`, `body`, `exit_names`, `lt`,
     `body'`, `ssa'`, `na'`] mp_tac) >>
  impl_tac
  >- gvs[word_state_eq_rel_def, dec_clock_def, strong_locals_rel_def] >>
  strip_tac >>
  first_x_assum (qspec_then `res'` mp_tac) >>
  disch_then (qspec_then `rcst` mp_tac) >>
  impl_tac
  >- (Cases_on `ssa_reconcile ssa' ssa_refreshed names = Skip` >> gvs[]
      >- ((* Skip case: derive cst' = brcst, then unfold STOP to match asm *)
          `cst' = brcst` by
            (qpat_x_assum `evaluate (Skip, brcst) = _` mp_tac >>
             simp[Once wordSemTheory.evaluate_def]) >>
          qpat_x_assum `cst' = brcst` (fn th => REWRITE_TAC [th]) >>
          qpat_x_assum `evaluate (STOP _, _) = _`
            (mp_tac o REWRITE_RULE [STOP_def]) >>
          rw[])
      >- ((* non-Skip case: body_final = Seq body' ssa_reconcile *)
          `evaluate (Seq body' (ssa_reconcile ssa' ssa_refreshed names),
                     cst with locals := env) = (NONE, cst')` by
            (simp[Once wordSemTheory.evaluate_def] >> gvs[]) >>
          gvs[wordSemTheory.cont_loop_def, wordSemTheory.fix_clock_def,
              STOP_def])) >>
  strip_tac >>
  Q.ISPECL_THEN
    [`body`, `st with <|locals := env'; permute := perm'|>`, `perm''`]
    assume_tac wordPropsTheory.permute_swap_lemma >>
  rfs[LET_THM] >>
  pop_assum mp_tac >>
  impl_keep_tac >- gvs[] >>
  strip_tac >>
  qexists_tac `perm'³'` >> simp[] >>
  simp[Once wordSemTheory.evaluate_def] >>
  simp[wordSemTheory.cut_state_def] >>
  `dec_clock (brst with permute := perm'') =
     dec_clock brst with permute := perm''`
    by simp[dec_clock_def] >>
  fs[STOP_def, wordSemTheory.cont_loop_def] >>
  gvs[]
)) >>
  Cases_on `x`
  >- ((* Result *)
      qexists_tac `perm'` >>
      simp[Once wordSemTheory.evaluate_def] >>
      `cut_state (names,LN) (st with permute := perm') =
         SOME (st with <|permute := perm'; locals := env'|>)` by
        fs[wordSemTheory.cut_state_def] >>
      Cases_on `ssa_reconcile ssa' ssa_refreshed names = Skip` >>
      gvs[wordSemTheory.cont_loop_def, wordSemTheory.exit_loop_def,
          wordSemTheory.evaluate_def])
  >- ((* Exception *)
      qexists_tac `perm'` >>
      simp[Once wordSemTheory.evaluate_def] >>
      `cut_state (names,LN) (st with permute := perm') =
         SOME (st with <|permute := perm'; locals := env'|>)` by
        fs[wordSemTheory.cut_state_def] >>
      Cases_on `ssa_reconcile ssa' ssa_refreshed names = Skip` >>
      gvs[wordSemTheory.cont_loop_def, wordSemTheory.exit_loop_def,
          wordSemTheory.evaluate_def])
  >- ((* Break n *)
      Cases_on `n`
      >- ((* Break 0: Loop catches Break 0, cuts on exit_names, returns NONE *)
          qexists_tac `perm'` >>
          simp[Once wordSemTheory.evaluate_def] >>
          `cut_state (names,LN) (st with permute := perm') =
             SOME (st with <|permute := perm'; locals := env'|>)` by
            fs[wordSemTheory.cut_state_def] >>
          Cases_on `ssa_reconcile ssa' ssa_refreshed names = Skip` >>
          gvs[wordSemTheory.cont_loop_def, wordSemTheory.exit_loop_def,
              wordSemTheory.evaluate_def, LLOOKUP_def,
              wordSemTheory.cut_state_def] >>
          (
  Cases_on `cut_env (exit_names,LN) brst.locals` >> gvs[] >>
  drule_at (Pos (el 2)) cut_env_lemma >>
  disch_then (qspecl_then [`brcst.locals`, `option_lookup ssa_refreshed`] mp_tac) >>
  impl_tac
  >- (simp[domain_union] >>
      fs[strong_locals_rel_def] >>
      rw[]) >>
  strip_tac >>
  gvs[apply_nummaps_key_def, apply_nummap_key_def, cut_env_fromAList_LN] >>
  conj_tac >- fs[word_state_eq_rel_def] >>
  simp[ssa_locals_rel_def] >>
  rw[] >>
  TRY (rename1 `_ ∈ domain ssa_refreshed` >>
       `x' ∈ domain x` by
         (rewrite_tac[sptreeTheory.domain_lookup] >>
          qexists_tac `y'` >> first_assum ACCEPT_TAC) >>
       `x' ∈ domain exit_names` by gvs[] >>
       fs[SUBSET_DEF] >> NO_TAC) >>
  TRY (rename1 `_ ∈ domain exit_names` >>
       `x' ∈ domain x` by
         (rewrite_tac[sptreeTheory.domain_lookup] >>
          qexists_tac `y'` >> first_assum ACCEPT_TAC) >>
       gvs[] >> NO_TAC) >>
  TRY (rename1 `lookup (THE _) y = SOME _` >>
       `x' ∈ domain x` by
         (rewrite_tac[sptreeTheory.domain_lookup] >>
          qexists_tac `y'` >> first_assum ACCEPT_TAC) >>
       `x' ∈ domain exit_names` by gvs[] >>
       `x' ∈ domain ssa_refreshed` by
         (qpat_x_assum `domain exit_names ⊆ domain ssa_refreshed`
            (assume_tac o SIMP_RULE std_ss [SUBSET_DEF]) >>
          first_x_assum drule >> simp[]) >>
       Cases_on `lookup x' ssa_refreshed`
       >- fs[sptreeTheory.domain_lookup] >>
       gvs[sptreeTheory.lookup_inter_alt] >>
       qpat_x_assum `strong_locals_rel _ _ x _`
         (mp_tac o REWRITE_RULE [strong_locals_rel_def]) >>
       disch_then (qspecl_then [`x'`, `y'`] mp_tac) >>
       simp[option_lookup_def] >> NO_TAC) >>
  TRY (rename1 `_ < na'` >>
       `x' ∈ domain x` by
         (rewrite_tac[sptreeTheory.domain_lookup] >>
          qexists_tac `y'` >> first_assum ACCEPT_TAC) >>
       `x' ∈ domain exit_names` by gvs[] >>
       `x' < na_refreshed` by fs[EVERY_MEM, toAList_domain] >>
       `ssa_map_ok na_refreshed (inter ssa_refreshed names)` by
         (irule ssa_map_ok_inter >> first_assum ACCEPT_TAC) >>
       drule ssa_cc_trans_props >>
       impl_tac >- gvs[] >>
       strip_tac >> gvs[] >> NO_TAC) >>
  TRY (rename1 `word_state_eq_rel _ _` >>
       fs[word_state_eq_rel_def] >> NO_TAC) >>
  ((* inter_dom: only inter_dom goals reach here *)
   qexists_tac `x'` >>
   gvs[option_lookup_def, sptreeTheory.lookup_inter_alt, AllCaseEqs()])
))
      >- (qexists_tac `perm'` >>
          simp[Once wordSemTheory.evaluate_def] >>
          `cut_state (names,LN) (st with permute := perm') =
             SOME (st with <|permute := perm'; locals := env'|>)` by
            fs[wordSemTheory.cut_state_def] >>
          Cases_on `ssa_reconcile ssa' ssa_refreshed names = Skip` >>
          gvs[wordSemTheory.cont_loop_def, wordSemTheory.exit_loop_def,
              wordSemTheory.evaluate_def, LLOOKUP_def]))
  >- ((* Continue n *)
      Cases_on `n`
      >- ((* Continue 0: cont_loop fires; recurse via clock-IH like NONE *)
          (
  qpat_x_assum `_ (ssa_cc_trans body _ _ _)` mp_tac >>
  simp[LLOOKUP_def] >>
  strip_tac >>
  `brst.clock = brcst.clock` by fs[word_state_eq_rel_def] >>
  Cases_on `brst.clock = 0`
  >- ((* TimeOut: clock=0 → both sides flush *)
      qexists_tac `perm'` >>
      simp[Once wordSemTheory.evaluate_def] >>
      `cut_state (names,LN) (st with permute := perm') =
         SOME (st with <|permute := perm'; locals := env'|>)` by
        fs[wordSemTheory.cut_state_def] >>
      Cases_on `ssa_reconcile ssa' ssa_refreshed names = Skip` >>
      gvs[wordSemTheory.cont_loop_def, wordSemTheory.exit_loop_def,
          wordSemTheory.flush_state_def, wordSemTheory.evaluate_def,
          word_state_eq_rel_def])
  >- ((* clock != 0: recursive via clock-IH *)
      Cases_on `ssa_reconcile ssa' ssa_refreshed names = Skip` >> fs[]
      >- ((* Skip case: body_final = body' *)
          gvs[wordSemTheory.cont_loop_def, wordSemTheory.exit_loop_def,
              STOP_def] >>
          Cases_on `cut_env (names, LN) brst.locals`
          >- ((* recursive cut fails: source returns Error *)
              qexists_tac `perm'` >>
              simp[Once wordSemTheory.evaluate_def] >>
              `cut_state (names,LN) (st with permute := perm') =
                 SOME (st with <|permute := perm'; locals := env'|>)` by
                fs[wordSemTheory.cut_state_def] >>
              simp[] >>
              `(brst with clock := brst.clock).clock ≠ 0` by simp[] >>
              gvs[wordSemTheory.fix_clock_def, wordSemTheory.cont_loop_def,
                  STOP_def, wordSemTheory.dec_clock_def] >>
              simp[Once wordSemTheory.evaluate_def,
                   wordSemTheory.cut_state_def]) >>
          (* recursive cut succeeds: apply IH *)
          imp_res_tac wordSemTheory.evaluate_clock >>
          `(dec_clock brcst).clock < cst.clock` by gvs[dec_clock_def] >>
          qpat_x_assum `∀m. m < cst.clock ⇒ _`
            (qspec_then `(dec_clock brcst).clock` mp_tac) >>
          impl_keep_tac >- simp[] >>
          disch_then (qspec_then `dec_clock brcst` mp_tac) >>
          simp[] >>
          `strong_locals_rel (option_lookup ssa_refreshed) (domain names)
             brst.locals brcst.locals` by
            (simp[strong_locals_rel_def] >> first_assum ACCEPT_TAC) >>
          `domain names ⊆ domain brst.locals` by
            (qpat_x_assum `cut_env (names,LN) brst.locals = _`
               (mp_tac o REWRITE_RULE [wordSemTheory.cut_env_def]) >>
             simp[AllCaseEqs()] >>
             rpt strip_tac >>
             drule cut_envs_domain_SUBSET >>
             strip_tac >> first_assum ACCEPT_TAC) >>
          `∀v. v ∈ domain names ⇒
                 option_lookup ssa_refreshed v ∈ domain brcst.locals` by
            (rpt strip_tac >>
             `∃v''. lookup v brst.locals = SOME v''` by
               (`v ∈ domain brst.locals` by
                  (qpat_x_assum `domain names ⊆ domain brst.locals` mp_tac >>
                   simp[SUBSET_DEF] >> disch_then drule >> simp[]) >>
                qpat_x_assum `v ∈ domain brst.locals` mp_tac >>
                simp[domain_lookup]) >>
             `lookup (option_lookup ssa_refreshed v) brcst.locals = SOME v''` by
               (qpat_x_assum `strong_locals_rel _ _ brst.locals brcst.locals`
                  (mp_tac o REWRITE_RULE [strong_locals_rel_def]) >>
                disch_then (qspecl_then [`v`, `v''`] mp_tac) >>
                impl_tac
                >- (conj_tac
                    >- first_assum ACCEPT_TAC
                    >- first_assum ACCEPT_TAC) >>
                strip_tac >> first_assum ACCEPT_TAC) >>
             simp[domain_lookup] >>
             qexists_tac `v''` >>
             first_assum ACCEPT_TAC) >>
          disch_then (qspecl_then
            [`dec_clock brst`, `ssa_refreshed`, `na_refreshed`,
             `names`, `body`, `exit_names`, `lt`,
             `body'`, `ssa'`, `na'`] mp_tac) >>
          impl_tac
          >- gvs[word_state_eq_rel_def, dec_clock_def, strong_locals_rel_def] >>
          strip_tac >>
          first_x_assum (qspec_then `res'` mp_tac) >>
          disch_then (qspec_then `rcst` mp_tac) >>
          impl_tac >- simp[] >>
          strip_tac >>
          Q.ISPECL_THEN
            [`body`, `st with <|locals := env'; permute := perm'|>`, `perm''`]
            assume_tac wordPropsTheory.permute_swap_lemma >>
          rfs[LET_THM] >>
          qexists_tac `perm'³'` >> simp[] >>
          simp[Once wordSemTheory.evaluate_def] >>
          simp[wordSemTheory.cut_state_def] >>
          `dec_clock (brst with permute := perm'') =
             dec_clock brst with permute := perm''`
            by simp[dec_clock_def] >>
          fs[STOP_def, wordSemTheory.cont_loop_def] >>
          gvs[])
      >- ((* non-Skip case: body_final = Seq body' ssa_reconcile *)
          `evaluate (Seq body' (ssa_reconcile ssa' ssa_refreshed names),
                     cst with locals := env) = (SOME (Continue 0), brcst)` by
            (simp[Once wordSemTheory.evaluate_def] >> gvs[]) >>
          fs[] >>
          gvs[wordSemTheory.cont_loop_def, wordSemTheory.exit_loop_def,
              STOP_def] >>
          Cases_on `cut_env (names, LN) brst.locals`
          >- ((* recursive cut fails: source returns Error *)
              qexists_tac `perm'` >>
              simp[Once wordSemTheory.evaluate_def] >>
              `cut_state (names,LN) (st with permute := perm') =
                 SOME (st with <|permute := perm'; locals := env'|>)` by
                fs[wordSemTheory.cut_state_def] >>
              simp[] >>
              `(brst with clock := brst.clock).clock ≠ 0` by simp[] >>
              gvs[wordSemTheory.fix_clock_def, wordSemTheory.cont_loop_def,
                  STOP_def, wordSemTheory.dec_clock_def] >>
              simp[Once wordSemTheory.evaluate_def,
                   wordSemTheory.cut_state_def]) >>
          imp_res_tac wordSemTheory.evaluate_clock >>
          `(dec_clock brcst).clock < cst.clock` by gvs[dec_clock_def] >>
          qpat_x_assum `∀m. m < cst.clock ⇒ _`
            (qspec_then `(dec_clock brcst).clock` mp_tac) >>
          impl_keep_tac >- simp[] >>
          disch_then (qspec_then `dec_clock brcst` mp_tac) >>
          simp[] >>
          `domain names ⊆ domain brst.locals` by
            (qpat_x_assum `cut_env (names,LN) brst.locals = _`
               (mp_tac o REWRITE_RULE [wordSemTheory.cut_env_def]) >>
             simp[AllCaseEqs()] >>
             rpt strip_tac >>
             drule cut_envs_domain_SUBSET >>
             strip_tac >> first_assum ACCEPT_TAC) >>
          `∀v. v ∈ domain names ⇒
                 option_lookup ssa_refreshed v ∈ domain brcst.locals` by
            (rpt strip_tac >>
             `∃v''. lookup v brst.locals = SOME v''` by
               (`v ∈ domain brst.locals` by
                  (qpat_x_assum `domain names ⊆ domain brst.locals` mp_tac >>
                   simp[SUBSET_DEF] >> disch_then drule >> simp[]) >>
                qpat_x_assum `v ∈ domain brst.locals` mp_tac >>
                simp[domain_lookup]) >>
             `lookup (option_lookup ssa_refreshed v) brcst.locals = SOME v''` by
               (qpat_x_assum `strong_locals_rel _ _ brst.locals brcst.locals`
                  (mp_tac o REWRITE_RULE [strong_locals_rel_def]) >>
                disch_then (qspecl_then [`v`, `v''`] mp_tac) >>
                impl_tac
                >- (conj_tac
                    >- first_assum ACCEPT_TAC
                    >- first_assum ACCEPT_TAC) >>
                strip_tac >> first_assum ACCEPT_TAC) >>
             simp[domain_lookup] >>
             qexists_tac `v''` >>
             first_assum ACCEPT_TAC) >>
          disch_then (qspecl_then
            [`dec_clock brst`, `ssa_refreshed`, `na_refreshed`,
             `names`, `body`, `exit_names`, `lt`,
             `body'`, `ssa'`, `na'`] mp_tac) >>
          impl_tac
          >- gvs[word_state_eq_rel_def, dec_clock_def, strong_locals_rel_def] >>
          strip_tac >>
          first_x_assum (qspec_then `res'` mp_tac) >>
          disch_then (qspec_then `rcst` mp_tac) >>
          impl_tac >- simp[] >>
          strip_tac >>
          Q.ISPECL_THEN
            [`body`, `st with <|locals := env'; permute := perm'|>`, `perm''`]
            assume_tac wordPropsTheory.permute_swap_lemma >>
          rfs[LET_THM] >>
          qexists_tac `perm'³'` >> simp[] >>
          simp[Once wordSemTheory.evaluate_def] >>
          simp[wordSemTheory.cut_state_def] >>
          `dec_clock (brst with permute := perm'') =
             dec_clock brst with permute := perm''`
            by simp[dec_clock_def] >>
          fs[STOP_def, wordSemTheory.cont_loop_def] >>
          gvs[]))
))
      >- (qexists_tac `perm'` >>
          simp[Once wordSemTheory.evaluate_def] >>
          `cut_state (names,LN) (st with permute := perm') =
             SOME (st with <|permute := perm'; locals := env'|>)` by
            fs[wordSemTheory.cut_state_def] >>
          Cases_on `ssa_reconcile ssa' ssa_refreshed names = Skip` >>
          gvs[wordSemTheory.cont_loop_def, wordSemTheory.exit_loop_def,
              wordSemTheory.evaluate_def, LLOOKUP_def]))
  >- ((* TimeOut *)
      qexists_tac `perm'` >>
      simp[Once wordSemTheory.evaluate_def] >>
      `cut_state (names,LN) (st with permute := perm') =
         SOME (st with <|permute := perm'; locals := env'|>)` by
        fs[wordSemTheory.cut_state_def] >>
      Cases_on `ssa_reconcile ssa' ssa_refreshed names = Skip` >>
      gvs[wordSemTheory.cont_loop_def, wordSemTheory.exit_loop_def,
          wordSemTheory.evaluate_def])
  >- ((* NotEnoughSpace *)
      qexists_tac `perm'` >>
      simp[Once wordSemTheory.evaluate_def] >>
      `cut_state (names,LN) (st with permute := perm') =
         SOME (st with <|permute := perm'; locals := env'|>)` by
        fs[wordSemTheory.cut_state_def] >>
      Cases_on `ssa_reconcile ssa' ssa_refreshed names = Skip` >>
      gvs[wordSemTheory.cont_loop_def, wordSemTheory.exit_loop_def,
          wordSemTheory.evaluate_def])
  >- ((* FinalFFI *)
      qexists_tac `perm'` >>
      simp[Once wordSemTheory.evaluate_def] >>
      `cut_state (names,LN) (st with permute := perm') =
         SOME (st with <|permute := perm'; locals := env'|>)` by
        fs[wordSemTheory.cut_state_def] >>
      Cases_on `ssa_reconcile ssa' ssa_refreshed names = Skip` >>
      gvs[wordSemTheory.cont_loop_def, wordSemTheory.exit_loop_def,
          wordSemTheory.evaluate_def])
  >- gvs[]  (* Error case: contradiction with bres ≠ SOME Error *));
val _ = print "loop_helper_full=";
val _ = print_thm ssa_cc_trans_Loop_helper;
val _ = print "\n";

(* Literal original local statements/proof scripts; no reference-tree exports. *)
val foldr_insert_const_swap = Q.prove (`  ∀rs h (v:'a word_loc) m.
    FOLDR (λr loc. insert r v loc) (insert h v m) rs =
    insert h v (FOLDR (λr loc. insert r v loc) m rs)`,
  Induct >> rw[] >>
  Cases_on `h = h'` >> simp[insert_swap]);
val evaluate_fake_const_chain = Q.prove (`  ∀rs (cst:('a,'b,'c) wordSem$state).
    evaluate (FOLDR Seq Skip (MAP (λr. (fake_move r):'a wordLang$prog) rs), cst) =
      (NONE, cst with locals := FOLDR (λr loc. insert r (Word 0w) loc) cst.locals rs)`,
  Induct
  >- simp[evaluate_def, wordSemTheory.state_component_equality] >>
  rpt strip_tac >>
  simp[evaluate_def, fake_move_def, inst_def, assign_def, word_exp_def,
       set_var_def] >>
  first_x_assum (qspec_then `cst with locals := insert h (Word 0w) cst.locals`
                            mp_tac) >>
  simp[fake_move_def, inst_def, assign_def, word_exp_def, set_var_def] >>
  disch_then kall_tac >>
  simp[foldr_insert_const_swap]);
val evaluate_fake_const_chain_locals = Q.prove (`  ∀rs (cst:('a,'b,'c) wordSem$state).
    let rcst = SND (evaluate (FOLDR Seq Skip
      (MAP (λr. (fake_move r):'a wordLang$prog) rs), cst)) in
    word_state_eq_rel cst rcst ∧
    domain rcst.locals = domain cst.locals ∪ set rs ∧
    (∀r. ¬ MEM r rs ⇒ lookup r rcst.locals = lookup r cst.locals) ∧
    (∀r. MEM r rs ⇒ lookup r rcst.locals = SOME (Word 0w))`,
  simp[evaluate_fake_const_chain] >>
  Induct >- simp[word_state_eq_rel_def] >>
  rpt strip_tac >> rpt conj_tac
  >- fs[word_state_eq_rel_def]
  >- (fs[EXTENSION] >> metis_tac[])
  >- (rw[lookup_insert] >> fs[] >>
      first_x_assum (qspec_then `cst` mp_tac) >> simp[])
  >- (rw[lookup_insert] >> fs[] >>
      first_x_assum (qspec_then `cst` mp_tac) >> simp[]));
val list_next_var_rename_lemma_1 = prove (``  ∀ls ssa na ls' ssa' na'.
  list_next_var_rename ls ssa na = (ls',ssa',na') ⇒
  let len = LENGTH ls in
  ALL_DISTINCT ls' ∧
  ls' = (MAP (λx. 4*x+na) (COUNT_LIST len)) ∧
  na' = na + 4* len``,
  Induct>>
  full_simp_tac(srw_ss())[list_next_var_rename_def,LET_THM,next_var_rename_def,COUNT_LIST_def]>>
  ntac 7 strip_tac>>
  srw_tac[][]>>
  Cases_on`list_next_var_rename ls (insert h na ssa) (na+4)`>>
  Cases_on`r`>>full_simp_tac(srw_ss())[]>>
  res_tac
  >-
    (`∀x. MEM x q ⇒ na < x` by
      (srw_tac[][MEM_MAP]>>DECIDE_TAC)>>
    qpat_x_assum`A = ls'` (sym_sub_tac)>>
    `¬ MEM na q` by
      (SPOSE_NOT_THEN assume_tac>>
      res_tac>>DECIDE_TAC)>>
    full_simp_tac(srw_ss())[ALL_DISTINCT])
  >-
    (full_simp_tac(srw_ss())[MAP_MAP_o]>>
    qpat_x_assum`A = ls'` sym_sub_tac>>
    full_simp_tac(srw_ss())[MAP_EQ_f]>>srw_tac[][]>>
    DECIDE_TAC)
  >>
    DECIDE_TAC);
val list_next_var_rename_lemma_2 = prove (``  ∀ls ssa na.
  ALL_DISTINCT ls ⇒
  let (ls',ssa',na') = list_next_var_rename ls ssa na in
  ls' = MAP (λx. THE(lookup x ssa')) ls ∧
  domain ssa' = domain ssa ∪ set ls ∧
  (∀x. ¬MEM x ls ⇒ lookup x ssa' = lookup x ssa) ∧
  (∀x. MEM x ls ⇒ ∃y. lookup x ssa' = SOME y)``,
  Induct>>full_simp_tac(srw_ss())[list_next_var_rename_def,LET_THM,next_var_rename_def]>>
  srw_tac[][]>>
  first_x_assum(qspecl_then[`insert h na ssa`,`na+4`] assume_tac)>>
  rev_full_simp_tac(srw_ss())[]>>
  Cases_on`list_next_var_rename ls (insert h na ssa) (na+4)`>>Cases_on`r`>>
  full_simp_tac(srw_ss())[lookup_insert,EXTENSION]>>srw_tac[][]>>
  metis_tac[]);
val get_vars_eq = prove (``  (set ls) SUBSET domain st.locals ==> ?z. get_vars ls st = SOME z /\
                                             z = MAP (\x. THE (lookup x st.locals)) ls``,
  Induct_on`ls`>>full_simp_tac(srw_ss())[get_vars_def,get_var_def]>>srw_tac[][]>>
  full_simp_tac(srw_ss())[domain_lookup]);
val option_lookup_subset_helper = prove (``  ∀ssa cst_locs ls.
    (∀x y. lookup x ssa = SOME y ⇒ y ∈ domain cst_locs) ∧
    set ls ⊆ domain ssa ⇒
    set (MAP (option_lookup ssa) ls) ⊆ domain cst_locs``,
  rw[SUBSET_DEF,MEM_MAP]>>
  `y ∈ domain ssa` by metis_tac[]>>
  fs[domain_lookup]>>
  rename1`lookup y ssa = SOME z`>>
  `option_lookup ssa y = z` by simp[option_lookup_def]>>
  res_tac>>fs[]);
val list_next_var_rename_move_preserve_weak = prove (``  ∀st ssa na ls cst.
  ssa_locals_rel na ssa st.locals cst.locals ∧
  set ls ⊆ domain ssa ∧
  ALL_DISTINCT ls ∧
  ssa_map_ok na ssa ∧
  word_state_eq_rel st cst
  ⇒
  let (mov,ssa',na') = list_next_var_rename_move ssa na ls in
  let (res,rcst) = evaluate (mov,cst) in
    res = NONE ∧
    ssa_locals_rel na' ssa' st.locals rcst.locals ∧
    word_state_eq_rel st rcst``,
  rpt strip_tac>>
  qabbrev_tac`cls = MAP (option_lookup ssa) ls`>>
  `set cls ⊆ domain cst.locals` by (
    simp[Abbr`cls`]>>
    irule option_lookup_subset_helper>>
    fs[ssa_locals_rel_def]>>
    metis_tac[])>>
  `LENGTH cls = LENGTH ls` by simp[Abbr`cls`]>>
  full_simp_tac(srw_ss())[list_next_var_rename_move_def,ssa_locals_rel_def]>>
  srw_tac[][]>>
  imp_res_tac list_next_var_rename_lemma_1>>
  imp_res_tac list_next_var_rename_lemma_2>>
  first_x_assum(qspecl_then[`ssa`,`na`] assume_tac)>>
  full_simp_tac(srw_ss())[LET_THM,evaluate_def]>>rev_full_simp_tac(srw_ss())[]>>
  rev_full_simp_tac(srw_ss())[MAP_ZIP,LENGTH_COUNT_LIST]>>full_simp_tac(srw_ss())[]>>
  imp_res_tac get_vars_eq>>
  qpat_x_assum`A=(res,rcst)` mp_tac>>
  full_simp_tac(srw_ss())[MAP_ZIP]>>srw_tac[][]
  >-
    (full_simp_tac(srw_ss())[set_vars_def,domain_alist_insert]>>
    Cases_on`MEM x ls`>>res_tac>>full_simp_tac(srw_ss())[]
    >-
      (DISJ2_TAC>>full_simp_tac(srw_ss())[MEM_MAP]>>
      HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[])
    >>
      (res_tac>>
      full_simp_tac(srw_ss())[]))
  >-
    (full_simp_tac(srw_ss())[set_vars_def,lookup_alist_insert]>>
    res_tac>>
    Cases_on`MEM x ls`>>full_simp_tac(srw_ss())[]
    >-
      (qsuff_tac `ALOOKUP (ZIP (MAP (λx. THE (lookup x ssa')) ls,
                                 MAP (λx. THE (lookup x cst.locals)) cls))
                          (THE (lookup x ssa')) = SOME y`
      >- rw[]>>
      match_mp_tac ALOOKUP_ALL_DISTINCT_MEM>>
      full_simp_tac(srw_ss())[MAP_ZIP]>>
      full_simp_tac(srw_ss())[MEM_EL]>>
      qexists_tac`n`>>
      full_simp_tac(srw_ss())[EL_ZIP,EL_MAP,Abbr`cls`]>>
      full_simp_tac(srw_ss())[domain_lookup,option_lookup_def]>>
      `THE (lookup (ls:num list)❲n❳ ssa) = v` by simp[]>>fs[])
    >>
      (full_simp_tac(srw_ss())[domain_lookup]>>
      qpat_abbrev_tac `opt:'a word_loc option = ALOOKUP (ZIP A) v`>>
      qsuff_tac `opt = NONE`
      >- (`THE (lookup x ssa) = v` by simp[]>>fs[Abbr`opt`])>>
      full_simp_tac(srw_ss())[Abbr`opt`]>>
      match_mp_tac (SPEC_ALL ALOOKUP_NONE|>REWRITE_RULE[EQ_IMP_THM]|>CONJ_PAIR|>snd)>>
      SPOSE_NOT_THEN assume_tac>>
      full_simp_tac(srw_ss())[MAP_ZIP]>>
      `v < na` by (full_simp_tac(srw_ss())[ssa_map_ok_def]>>res_tac)>>
      rev_full_simp_tac(srw_ss())[]>>
      rpt (qpat_x_assum`A = B` sym_sub_tac)>>
      full_simp_tac(srw_ss())[MEM_MAP]>>
      Cases_on`y`>>gvs[MEM_ZIP,EL_MAP,EL_COUNT_LIST,LENGTH_COUNT_LIST]))
  >-
    (res_tac>>DECIDE_TAC)
  >-
    full_simp_tac(srw_ss())[word_state_eq_rel_def,set_vars_def]);
val is_alloc_var_add = GEN_ALL (prove (``is_alloc_var na ⇒ is_alloc_var (na+4)``,
  full_simp_tac(srw_ss())[is_alloc_var_def]>>
  (qspec_then `4` assume_tac arithmeticTheory.MOD_PLUS>>full_simp_tac(srw_ss())[]>>
    pop_assum (qspecl_then [`na`,`4`] assume_tac)>>
    rev_full_simp_tac(srw_ss())[])));
val is_stack_var_add = GEN_ALL (prove (``is_stack_var na ⇒ is_stack_var (na+4)``,
  full_simp_tac(srw_ss())[is_stack_var_def]>>
  (qspec_then `4` assume_tac arithmeticTheory.MOD_PLUS>>full_simp_tac(srw_ss())[]>>
    pop_assum (qspecl_then [`na`,`4`] assume_tac)>>
    rev_full_simp_tac(srw_ss())[])));
val list_next_var_rename_props = GEN_ALL (prove (``∀ls ssa na ls' ssa' na'.
  list_next_var_rename ls ssa na = (ls',ssa',na') ==>
  (is_alloc_var na ∨ is_stack_var na) ∧
  ssa_map_ok na ssa
  ⇒
  na ≤ na' ∧
  (is_alloc_var na ⇒ is_alloc_var na') ∧
  (is_stack_var na ⇒ is_stack_var na') ∧
  ssa_map_ok na' ssa'``,
  Induct>>full_simp_tac(srw_ss())[list_next_var_rename_def,next_var_rename_def]>>
  LET_ELIM_TAC>>
  first_x_assum(qspecl_then[`ssa''`,`na''`,`ys`,`ssa'''`,`na'''`]
    mp_tac)>>
  (impl_tac>-simp[] >>
   impl_tac >-
    (full_simp_tac(srw_ss())[ssa_map_ok_def]>>srw_tac[][]
    >-
      metis_tac[is_alloc_var_add,is_stack_var_add]
    >-
      (full_simp_tac(srw_ss())[lookup_insert]>>Cases_on`x=h`>>full_simp_tac(srw_ss())[]>>
      metis_tac[convention_partitions])
    >-
      (full_simp_tac(srw_ss())[lookup_insert]>>Cases_on`x=h`>>full_simp_tac(srw_ss())[]>>
      res_tac>>DECIDE_TAC)))>>
  srw_tac[][]>> TRY(DECIDE_TAC)>> full_simp_tac(srw_ss())[]>>
  metis_tac[is_alloc_var_add,is_stack_var_add]));



val list_next_var_rename_move_props = GEN_ALL (prove (``∀ls ssa na ls' ssa' na'.
  list_next_var_rename_move ssa na ls = (ls',ssa',na') ==>
  (is_alloc_var na ∨ is_stack_var na) ∧
  ssa_map_ok na ssa
  ⇒
  na ≤ na' ∧
  (is_alloc_var na ⇒ is_alloc_var na') ∧
  (is_stack_var na ⇒ is_stack_var na') ∧
  ssa_map_ok na' ssa'``,
  full_simp_tac(srw_ss())[list_next_var_rename_move_def]>>LET_ELIM_TAC>>
  full_simp_tac(srw_ss())[]>>
  imp_res_tac list_next_var_rename_props));






val INJ_less = Q.prove (`INJ f s' UNIV ∧ s ⊆ s' ⇒ INJ f s UNIV`,metis_tac[INJ_DEF,SUBSET_DEF]);
val loop_setup_correct = Q.prove (`  ∀ (st:('a,'b,'c) wordSem$state) cst ssa na names exit_names
    setup_prog ssa_refreshed na_refreshed.
    word_state_eq_rel st cst ∧
    ssa_locals_rel na ssa st.locals cst.locals ∧
    ssa_map_ok na ssa ∧
    is_alloc_var na ∧
    loop_setup names exit_names ssa na = (setup_prog,ssa_refreshed,na_refreshed) ⇒
    ∃rcst.
      evaluate (setup_prog, cst) = (NONE,rcst) ∧
      word_state_eq_rel st rcst ∧
      ssa_locals_rel na_refreshed ssa_refreshed st.locals rcst.locals ∧
      na ≤ na_refreshed ∧
      is_alloc_var na_refreshed ∧
      ssa_map_ok na_refreshed ssa_refreshed ∧
      domain ssa_refreshed = domain ssa ∪ domain (union names exit_names) ∧
      INJ (option_lookup ssa_refreshed) (domain names) UNIV ∧
      INJ (option_lookup ssa_refreshed) (domain exit_names) UNIV ∧
      (∀v. v ∈ domain ssa_refreshed ⇒
        option_lookup ssa_refreshed v ∈ domain rcst.locals)`,
  rpt strip_tac >>
  fs[loop_setup_def] >>
  pairarg_tac >> fs[] >>
  pairarg_tac >> fs[] >>
  rveq >>
  qabbrev_tac
    `extend_ls = FILTER (λv. lookup v ssa = NONE)
       (MAP FST (toAList (union names exit_names)))` >>
  qabbrev_tac
    `refresh_ls = FILTER (λv. IS_SOME (lookup v ssa))
       (MAP FST (toAList (union names exit_names)))` >>
  `ALL_DISTINCT extend_ls ∧ ALL_DISTINCT refresh_ls` by (
    unabbrev_all_tac >> conj_tac >> irule FILTER_ALL_DISTINCT >>
    simp[ALL_DISTINCT_MAP_FST_toAList]) >>
  `set extend_ls ∩ set refresh_ls = ∅` by (
    unabbrev_all_tac >>
    simp[EXTENSION, MEM_FILTER] >> metis_tac[NOT_SOME_NONE]) >>
  `set extend_ls ∪ set refresh_ls = domain (union names exit_names)` by (
    unabbrev_all_tac >>
    simp[EXTENSION, MEM_FILTER, MEM_MAP, MEM_toAList,
         EXISTS_PROD, domain_lookup] >>
    metis_tac[option_CASES, IS_SOME_DEF]) >>
  qpat_x_assum `list_next_var_rename extend_ls _ _ = _` assume_tac >>
  drule_then assume_tac list_next_var_rename_props >>
  rfs[] >>
  drule_then assume_tac list_next_var_rename_lemma_1 >>
  fs[LET_THM] >>
  qspecl_then [`extend_ls`, `ssa`, `na`] mp_tac list_next_var_rename_lemma_2 >>
  simp[LET_THM] >> strip_tac >>
  (* fake_prog evaluation *)
  mp_tac (Q.SPECL [`fresh_pos_ls`, `cst`]
    (INST_TYPE [beta |-> ``:'b``, gamma |-> ``:'c``] evaluate_fake_const_chain)) >>
  qmatch_goalsub_abbrev_tac `(NONE, fake_cst)` >>
  strip_tac >>
  mp_tac (Q.SPECL [`fresh_pos_ls`, `cst`]
    (INST_TYPE [beta |-> ``:'b``, gamma |-> ``:'c``] evaluate_fake_const_chain_locals)) >>
  simp[] >> strip_tac >>
  `word_state_eq_rel st fake_cst` by (
    simp[Abbr `fake_cst`] >> fs[word_state_eq_rel_def]) >>
  `ssa_locals_rel na_ext ssa_ext st.locals fake_cst.locals`
    by (
  simp[ssa_locals_rel_def] >>
  conj_tac
  >- (rpt strip_tac >>
      Cases_on `MEM x extend_ls`
      >- (`MEM y (MAP (λx. THE (lookup x ssa_ext)) extend_ls)` by (
            simp[MEM_MAP] >> qexists_tac `x` >> simp[]) >>
          metis_tac[domain_lookup, IS_SOME_DEF])
      >- (`lookup x ssa = SOME y` by metis_tac[] >>
          `y ∈ domain cst.locals` by (
            fs[ssa_locals_rel_def] >> metis_tac[]) >>
          fs[])) >>
  ntac 2 gen_tac >> strip_tac >>
  `x ∈ domain ssa ∧ lookup (THE (lookup x ssa)) cst.locals = SOME y ∧
   (is_alloc_var x ⇒ x < na)` by (fs[ssa_locals_rel_def] >> metis_tac[]) >>
  `¬MEM x extend_ls` by (
    unabbrev_all_tac >> simp[MEM_FILTER] >>
    fs[domain_lookup, IS_SOME_EXISTS]) >>
  `lookup x ssa_ext = lookup x ssa` by metis_tac[] >>
  rpt conj_tac
  >- (`x ∈ domain ssa_ext` by (
        qpat_x_assum `domain ssa_ext = _` SUBST1_TAC >> simp[]) >>
      simp[])
  >- (`∃z. lookup x ssa = SOME z` by fs[domain_lookup] >>
      `THE (lookup x ssa) < na`
        by (fs[ssa_map_ok_def] >> res_tac >> simp[]) >>
      `¬MEM (THE (lookup x ssa)) fresh_pos_ls` by (
        qpat_x_assum `fresh_pos_ls = _` SUBST1_TAC >>
        simp[MEM_MAP, MEM_COUNT_LIST] >>
        rpt strip_tac >> gvs[]) >>
      `¬MEM (THE (lookup x ssa)) (MAP (λx. THE (lookup x ssa_ext)) extend_ls)`
        by metis_tac[] >>
      `lookup (THE (lookup x ssa)) fake_cst.locals =
       lookup (THE (lookup x ssa)) cst.locals` by metis_tac[] >>
      metis_tac[])
  >- (strip_tac >> res_tac >> DECIDE_TAC)
) >>
  `set refresh_ls ⊆ domain ssa_ext` by (
    fs[SUBSET_DEF, EXTENSION] >>
    `∀v. MEM v refresh_ls ⇒ MEM v (MAP FST (toAList (union names exit_names)))`
      by (unabbrev_all_tac >> simp[MEM_FILTER]) >>
    `∀v. MEM v refresh_ls ⇒ v ∈ domain ssa` by (
      unabbrev_all_tac >>
      simp[MEM_FILTER, domain_lookup, IS_SOME_EXISTS] >>
      metis_tac[]) >>
    metis_tac[]) >>
  qspecl_then [`st`, `ssa_ext`, `na_ext`, `refresh_ls`, `fake_cst`]
    mp_tac list_next_var_rename_move_preserve_weak >>
  simp[] >>
  pairarg_tac >> fs[] >>
  strip_tac >>
  qpat_x_assum `list_next_var_rename_move ssa_ext _ refresh_ls = _`
    assume_tac >>
  drule_then assume_tac list_next_var_rename_move_props >>
  rfs[] >>
  fs[list_next_var_rename_move_def] >>
  pairarg_tac >> fs[] >> rveq >>
  qpat_x_assum `list_next_var_rename refresh_ls _ _ = _` assume_tac >>
  drule_then assume_tac list_next_var_rename_lemma_1 >>
  qspecl_then [`refresh_ls`, `ssa_ext`, `na + 4 * LENGTH extend_ls`]
    mp_tac list_next_var_rename_lemma_2 >>
  fs[LET_THM] >> rfs[] >> strip_tac >>
  qexists_tac `rcst` >>
  qpat_x_assum `new_ls = _` (assume_tac o GSYM) >> fs[] >>
  `∀v. MEM v extend_ls ⇒
       ∃idx. idx < LENGTH extend_ls ∧
             option_lookup ssa' v = na + 4 * idx`
    by (
  rpt strip_tac >>
  `∃idx. idx < LENGTH extend_ls ∧ EL idx extend_ls = v` by metis_tac[MEM_EL] >>
  qexists_tac `idx` >> simp[] >>
  `¬MEM v refresh_ls` by (fs[EXTENSION] >> metis_tac[]) >>
  `lookup v ssa' = lookup v ssa_ext` by metis_tac[] >>
  `∃y. lookup v ssa_ext = SOME y` by metis_tac[] >>
  simp[option_lookup_def] >>
  `THE (lookup v ssa_ext) = EL idx (MAP (λx. THE (lookup x ssa_ext)) extend_ls)`
    by simp[EL_MAP] >>
  rfs[] >>
  qpat_x_assum `MAP (λx. na + 4 * x) _ = _` (SUBST1_TAC o GSYM) >>
  DEP_REWRITE_TAC[EL_MAP, EL_COUNT_LIST] >> simp[LENGTH_COUNT_LIST]
) >>
  `∀v. MEM v refresh_ls ⇒
       ∃j. j < LENGTH refresh_ls ∧
           option_lookup ssa' v = na + 4 * LENGTH extend_ls + 4 * j`
    by (
  rpt strip_tac >>
  `∃j. j < LENGTH refresh_ls ∧ EL j refresh_ls = v` by metis_tac[MEM_EL] >>
  qexists_tac `j` >> simp[] >>
  `∃y. lookup v ssa' = SOME y` by metis_tac[] >>
  simp[option_lookup_def] >>
  `THE (lookup v ssa') = EL j (MAP (λx. THE (lookup x ssa')) refresh_ls)`
    by simp[EL_MAP] >>
  rfs[] >>
  qpat_x_assum `MAP (λx. na + (4 * x + 4 * LENGTH extend_ls)) _ = _`
    (SUBST1_TAC o GSYM) >>
  DEP_REWRITE_TAC[EL_MAP, EL_COUNT_LIST] >> simp[LENGTH_COUNT_LIST]
) >>
  `INJ (option_lookup ssa') (set extend_ls ∪ set refresh_ls) UNIV`
    by (
  simp[INJ_DEF] >>
  `∀v ix. MEM v extend_ls ∧ ix < LENGTH extend_ls ∧ EL ix extend_ls = v ⇒
          option_lookup ssa' v = na + 4 * ix` by (
    rpt strip_tac >>
    `¬MEM v refresh_ls` by (fs[EXTENSION] >> metis_tac[]) >>
    `lookup v ssa' = lookup v ssa_ext` by metis_tac[] >>
    `∃z. lookup v ssa_ext = SOME z` by metis_tac[] >>
    simp[option_lookup_def] >>
    `THE (lookup v ssa_ext) = EL ix (MAP (λx. THE (lookup x ssa_ext)) extend_ls)`
      by simp[EL_MAP] >>
    rfs[] >>
    qpat_x_assum `MAP (λx. na + 4 * x) _ = _` (SUBST1_TAC o GSYM) >>
    DEP_REWRITE_TAC[EL_MAP, EL_COUNT_LIST] >> simp[LENGTH_COUNT_LIST]) >>
  `∀v iy. MEM v refresh_ls ∧ iy < LENGTH refresh_ls ∧ EL iy refresh_ls = v ⇒
          option_lookup ssa' v = na + 4 * LENGTH extend_ls + 4 * iy` by (
    rpt strip_tac >>
    `∃z. lookup v ssa' = SOME z` by metis_tac[] >>
    simp[option_lookup_def] >>
    `THE (lookup v ssa') = EL iy (MAP (λx. THE (lookup x ssa')) refresh_ls)`
      by simp[EL_MAP] >>
    rfs[] >>
    qpat_x_assum `MAP (λx. na + (4 * x + 4 * LENGTH extend_ls)) _ = _`
      (SUBST1_TAC o GSYM) >>
    DEP_REWRITE_TAC[EL_MAP, EL_COUNT_LIST] >> simp[LENGTH_COUNT_LIST]) >>
  ntac 2 gen_tac >>
  disch_then (CONJUNCTS_THEN assume_tac) >>
  disch_tac >>
  Cases_on `MEM x extend_ls`
  >- (Cases_on `MEM y extend_ls`
      >- (`∃ix. ix < LENGTH extend_ls ∧ EL ix extend_ls = x` by metis_tac[MEM_EL] >>
          `∃iy. iy < LENGTH extend_ls ∧ EL iy extend_ls = y` by metis_tac[MEM_EL] >>
          `option_lookup ssa' x = na + 4 * ix` by metis_tac[] >>
          `option_lookup ssa' y = na + 4 * iy` by metis_tac[] >>
          `na + 4 * ix = na + 4 * iy` by metis_tac[] >>
          `ix = iy` by gs[] >>
          metis_tac[])
      >- (`MEM y refresh_ls` by fs[] >>
          `∃ix. ix < LENGTH extend_ls ∧ EL ix extend_ls = x` by metis_tac[MEM_EL] >>
          `∃iy. iy < LENGTH refresh_ls ∧ EL iy refresh_ls = y` by metis_tac[MEM_EL] >>
          `option_lookup ssa' x = na + 4 * ix` by metis_tac[] >>
          `option_lookup ssa' y = na + 4 * LENGTH extend_ls + 4 * iy` by metis_tac[] >>
          `na + 4 * ix = na + 4 * LENGTH extend_ls + 4 * iy` by metis_tac[] >>
          `F` by gs[] >>
          fs[]))
  >- (`MEM x refresh_ls` by fs[] >>
      Cases_on `MEM y refresh_ls`
      >- (`∃ix. ix < LENGTH refresh_ls ∧ EL ix refresh_ls = x` by metis_tac[MEM_EL] >>
          `∃iy. iy < LENGTH refresh_ls ∧ EL iy refresh_ls = y` by metis_tac[MEM_EL] >>
          `option_lookup ssa' x = na + 4 * LENGTH extend_ls + 4 * ix` by metis_tac[] >>
          `option_lookup ssa' y = na + 4 * LENGTH extend_ls + 4 * iy` by metis_tac[] >>
          `na + 4 * LENGTH extend_ls + 4 * ix =
           na + 4 * LENGTH extend_ls + 4 * iy` by metis_tac[] >>
          `ix = iy` by gs[] >>
          metis_tac[])
      >- (`MEM y extend_ls` by fs[] >>
          `∃ix. ix < LENGTH refresh_ls ∧ EL ix refresh_ls = x` by metis_tac[MEM_EL] >>
          `∃iy. iy < LENGTH extend_ls ∧ EL iy extend_ls = y` by metis_tac[MEM_EL] >>
          `option_lookup ssa' x = na + 4 * LENGTH extend_ls + 4 * ix` by metis_tac[] >>
          `option_lookup ssa' y = na + 4 * iy` by metis_tac[] >>
          `na + 4 * LENGTH extend_ls + 4 * ix = na + 4 * iy` by metis_tac[] >>
          `F` by gs[] >>
          fs[]))
) >>
  `domain names ⊆ set extend_ls ∪ set refresh_ls ∧
   domain exit_names ⊆ set extend_ls ∪ set refresh_ls` by (
    fs[SUBSET_DEF] >> rpt strip_tac >>
    `x ∈ domain (union names exit_names)` by (
      simp[domain_union] >> metis_tac[]) >>
    metis_tac[IN_UNION]) >>
  rpt conj_tac
  >- simp[evaluate_def]
  >- (qpat_x_assum `set extend_ls ∪ set refresh_ls = _`
        (assume_tac o GSYM) >> fs[AC UNION_ASSOC UNION_COMM])
  >- (irule INJ_less >>
      qexists_tac `set extend_ls ∪ set refresh_ls` >> simp[])
  >- (irule INJ_less >>
      qexists_tac `set extend_ls ∪ set refresh_ls` >> simp[])
  >- (
  rpt strip_tac >>
  `∃y. lookup v ssa' = SOME y` by (
    Cases_on `MEM v refresh_ls` >- metis_tac[] >>
    `lookup v ssa' = lookup v ssa_ext` by metis_tac[] >>
    `v ∈ domain ssa_ext` by (
      qpat_x_assum `domain ssa_ext = _` SUBST1_TAC >>
      simp[] >> fs[]) >>
    fs[domain_lookup]) >>
  fs[option_lookup_def, ssa_locals_rel_def] >>
  metis_tac[]
));

val evaluate_seq_collapse = Q.prove (`  evaluate (P, s) = (NONE, t) ⇒
  evaluate (Seq P Q, s) = evaluate (Q, t)`,
  simp[evaluate_def]);
val body_statement = Q.SPEC `body` ssa_cc_trans_correct;
val loop_statement = Q.SPEC `Loop names body exit_names` ssa_cc_trans_correct;
val loop_case = prove(mk_imp(concl body_statement,concl loop_statement), rpt strip_tac >>
  rename1 `Loop names body exit_names` >>
  qpat_x_assum `every_var _ _` mp_tac >> simp[every_var_def] >> strip_tac >>
  simp[ssa_cc_trans_def] >>
  rpt (pairarg_tac >> fs[]) >>
  drule_then drule loop_setup_correct >>
  rpt (disch_then drule) >>
  strip_tac >>
  drule evaluate_seq_collapse >>
  strip_tac >>
  qpat_x_assum `inter ssa_refreshed exit_names = ssa'` (assume_tac o GSYM) >>
  qpat_x_assum `na'' = na'` (assume_tac o GSYM) >>
  fs[] >>
  `domain names ⊆ domain ssa_refreshed ∧
   domain exit_names ⊆ domain ssa_refreshed` by (
    qpat_x_assum `domain ssa_refreshed = _` SUBST1_TAC >>
    simp[domain_union, SUBSET_DEF]) >>
  `strong_locals_rel (option_lookup ssa_refreshed) (domain names)
     st.locals rcst'.locals` by (
    rw[strong_locals_rel_def] >>
    `n ∈ domain ssa_refreshed ∧
     lookup (THE (lookup n ssa_refreshed)) rcst'.locals = SOME v` by
      (conj_asm1_tac >- fs[SUBSET_DEF] >>
       fs[ssa_locals_rel_def] >> res_tac >> simp[]) >>
    Cases_on `lookup n ssa_refreshed` >- fs[domain_lookup] >>
    fs[option_lookup_def]) >>
  qspecl_then
    [`st`, `rcst'`, `ssa_refreshed`, `na_refreshed`, `names`, `body`,
     `exit_names`, `lt`, `body'`, `ssa''`, `na''`]
    mp_tac ssa_cc_trans_Loop_helper >>
  impl_tac
  >- (rpt conj_tac >> fs[]
      >- (rpt strip_tac >>
          first_x_assum irule >> fs[SUBSET_DEF])
      >- (irule every_var_mono >>
          qexists_tac `λx. x < na` >> fs[])
      >- (irule MONO_EVERY >>
          qexists_tac `λx. x < na` >> fs[])
      >- (irule MONO_EVERY >>
          qexists_tac `λx. x < na` >> fs[])) >>
  simp[LET_DEF] >>
  disch_then (qspecl_then [`res'`, `rcst`] mp_tac) >>
  impl_tac
  >- (qpat_x_assum `Seq setup_prog _ = prog'` (assume_tac o SYM) >>
      fs[] >>
      qpat_x_assum `∀Q. evaluate (Seq _ _, _) = _` (fn th =>
        once_rewrite_tac [GSYM th]) >>
      first_x_assum ACCEPT_TAC) >>
  simp[]);
val _ = print "loop_case_full=";
val _ = print_thm loop_case;
val _ = print "\n";
