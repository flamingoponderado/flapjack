load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory word_allocTheory wordSemTheory wordPropsTheory wordLangTheory sptreeTheory reg_allocTheory;
val _ = Globals.linewidth := 1000;
open wordConvsTheory;
val ssa_locals_rel_more = prove (``ssa_locals_rel na ssa stlocs cstlocs ∧ na ≤ na' ⇒
  ssa_locals_rel na' ssa stlocs cstlocs``,
  srw_tac[][ssa_locals_rel_def] >> full_simp_tac(srw_ss())[] >- metis_tac[] >>
  res_tac >> full_simp_tac(srw_ss())[] >> DECIDE_TAC);
val ssa_map_ok_more = prove (``ssa_map_ok na ssa ∧ na ≤ na' ⇒ ssa_map_ok na' ssa``,
  rw[ssa_map_ok_def] >> res_tac >> fs[] >> DECIDE_TAC);
val ssa_locals_rel_get_var = prove (``ssa_locals_rel na ssa st.locals cst.locals ∧
  get_var n st = SOME x
  ⇒
  get_var (option_lookup ssa n) cst = SOME x``,
  full_simp_tac(srw_ss())[get_var_def,ssa_locals_rel_def,strong_locals_rel_def,option_lookup_def]>>
  srw_tac[][]>>
  FULL_CASE_TAC>>full_simp_tac(srw_ss())[domain_lookup]>>
  first_x_assum(qspecl_then[`n`,`x`] assume_tac)>>rev_full_simp_tac(srw_ss())[]);
val ssa_map_ok_extend = GEN_ALL (prove (``ssa_map_ok na ssa ∧
  ¬is_phy_var na ⇒
  ssa_map_ok (na+4) (insert h na ssa)``,
  full_simp_tac(srw_ss())[ssa_map_ok_def]>>
  srw_tac[][]>>full_simp_tac(srw_ss())[lookup_insert]>>
  Cases_on`x=h`>>full_simp_tac(srw_ss())[]>>
  res_tac>-
    DECIDE_TAC));
val merge_moves_frame = GEN_ALL (prove (``∀ls na ssaL ssaR.
  is_alloc_var na
  ⇒
  let(moveL,moveR,na',ssaL',ssaR') = merge_moves ls ssaL ssaR na in
  is_alloc_var na' ∧
  na ≤ na' ∧
  (ssa_map_ok na ssaL ⇒ ssa_map_ok na' ssaL') ∧
  (ssa_map_ok na ssaR ⇒ ssa_map_ok na' ssaR')``,
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
  metis_tac[ssa_map_ok_extend,convention_partitions]));
val merge_moves_fst = GEN_ALL (prove (``∀ls na ssaL ssaR.
  let(moveL,moveR,na',ssaL',ssaR') = merge_moves ls ssaL ssaR na in
  na ≤ na' ∧
  EVERY (λx. x < na' ∧ x ≥ na) (MAP FST moveL) ∧
  EVERY (λx. x < na' ∧ x ≥ na) (MAP FST moveR)``,
  Induct>>full_simp_tac(srw_ss())[merge_moves_def]>>srw_tac[][]>>
  full_simp_tac(srw_ss())[EVERY_MAP]>>
  first_x_assum(qspecl_then[`na`,`ssaL`,`ssaR`]assume_tac)>>
  rev_full_simp_tac(srw_ss())[LET_THM]>>
  EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
  qpat_x_assum`A = moveL` (sym_sub_tac)>>
  qpat_x_assum`A = moveR` (sym_sub_tac)>>
  full_simp_tac(srw_ss())[EVERY_MEM]>>srw_tac[][]>>
  res_tac>>
  DECIDE_TAC));
val mov_eval_head = GEN_ALL (prove (``evaluate(Move p moves,st) = (NONE,rst) ∧
  y ∈ domain st.locals ∧
  ¬MEM y (MAP FST moves) ∧
  ¬MEM x (MAP FST moves)
  ⇒
  evaluate(Move p ((x,y)::moves),st) = (NONE, rst with locals:=insert x (THE (lookup y st.locals)) rst.locals)``,
  full_simp_tac(srw_ss())[evaluate_def,get_vars_def,get_var_def,domain_lookup]>>
  EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
  strip_tac>>
  full_simp_tac(srw_ss())[set_vars_def,alist_insert_def]>>
  qpat_x_assum `A=rst` (sym_sub_tac)>>full_simp_tac(srw_ss())[]));
val merge_moves_correctL = GEN_ALL (prove (``∀ls na ssaL ssaR stL cstL pri.
  is_alloc_var na ∧
  ALL_DISTINCT ls ∧
  ssa_map_ok na ssaL
  ⇒
  let(moveL,moveR,na',ssaL',ssaR') = merge_moves ls ssaL ssaR na in
  (ssa_locals_rel na ssaL stL.locals cstL.locals ⇒
  let (resL,rcstL) = evaluate(Move pri moveL,cstL) in
    resL = NONE ∧
    (∀x. ¬MEM x ls ⇒ lookup x ssaL' = lookup x ssaL) ∧
    (∀x y. (x < na ∧ lookup x cstL.locals = SOME y)
    ⇒  lookup x rcstL.locals = SOME y) ∧
    ssa_locals_rel na' ssaL' stL.locals rcstL.locals ∧
    word_state_eq_rel cstL rcstL)``,
  Induct>>full_simp_tac(srw_ss())[merge_moves_def]>-
  (srw_tac[][]>>
  full_simp_tac(srw_ss())[evaluate_def,word_state_eq_rel_def,get_vars_def,set_vars_def,alist_insert_def]>>
  rev_full_simp_tac(srw_ss())[]>>srw_tac[][])>>
  rpt strip_tac>>
  first_x_assum(qspecl_then[`na`,`ssaL`,`ssaR`,`stL`,`cstL`,`pri`]mp_tac)>>
  impl_tac>-
    (rev_full_simp_tac(srw_ss())[LET_THM]>>
    metis_tac[])>>
  strip_tac>>
  rev_full_simp_tac(srw_ss())[LET_THM]>>
  Cases_on`merge_moves ls ssaL ssaR na`>>PairCases_on`r`>>full_simp_tac(srw_ss())[]>>
  EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
  strip_tac>>full_simp_tac(srw_ss())[]>>
  Cases_on`evaluate(Move pri q,cstL)`>>full_simp_tac(srw_ss())[]>>
  imp_res_tac merge_moves_frame>>
  pop_assum(qspecl_then[`ssaR`,`ssaL`,`ls`]assume_tac)>>
  Q.ISPECL_THEN [`ls`,`na`,`ssaL`,`ssaR`] assume_tac merge_moves_fst>>
  rev_full_simp_tac(srw_ss())[LET_THM]>>
  imp_res_tac mov_eval_head>>
  pop_assum(qspec_then`r1` mp_tac)>>impl_tac>-
    (SPOSE_NOT_THEN assume_tac>>full_simp_tac(srw_ss())[EVERY_MEM]>>
    res_tac>>
    DECIDE_TAC)>>
  strip_tac>>
  pop_assum(qspec_then`x'` mp_tac)>>impl_tac>-
    (SPOSE_NOT_THEN assume_tac>>full_simp_tac(srw_ss())[EVERY_MEM,ssa_map_ok_def]>>
    res_tac>>
    DECIDE_TAC)>>
  impl_tac>-
    (full_simp_tac(srw_ss())[ssa_locals_rel_def]>>
    metis_tac[])>>
  strip_tac>>
  srw_tac[][]>>full_simp_tac(srw_ss())[lookup_insert]
  >-
    (`x'' ≠ r1` by DECIDE_TAC>>
    full_simp_tac(srw_ss())[lookup_insert])
  >-
    (full_simp_tac(srw_ss())[ssa_locals_rel_def]>>
    srw_tac[][]>>full_simp_tac(srw_ss())[lookup_insert]
    >-
      (Cases_on`x''=h`>>full_simp_tac(srw_ss())[]>>
      metis_tac[])
    >-
      (Cases_on`x''=h`>>full_simp_tac(srw_ss())[]>-
      (res_tac>>full_simp_tac(srw_ss())[]>>
      qpat_x_assum`lookup h ssaL = SOME x'` (SUBST_ALL_TAC)>>
      full_simp_tac(srw_ss())[])>>
      res_tac>>
      full_simp_tac(srw_ss())[domain_lookup]>>
       `v'' < r1` by
        (full_simp_tac(srw_ss())[ssa_map_ok_def]>>
        metis_tac[])>>
      `v'' ≠ r1` by DECIDE_TAC>>
      full_simp_tac(srw_ss())[])
    >-
      (res_tac>>DECIDE_TAC))
  >>
      full_simp_tac(srw_ss())[word_state_eq_rel_def]));

val fake_moves_frame = prove (``  ∀ls na ssaL ssaR.
  is_alloc_var na
  ⇒
  let(moveL,moveR,na',ssaL',ssaR') = fake_moves prio ls ssaL ssaR na in
  is_alloc_var na' ∧
  na ≤ na' ∧
  (ssa_map_ok na ssaL ⇒ ssa_map_ok na' ssaL') ∧
  (ssa_map_ok na ssaR ⇒ ssa_map_ok na' ssaR')``,
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
val fake_moves_correctL = prove (``  ∀ls na ssaL ssaR stL cstL.
  is_alloc_var na ∧
  ALL_DISTINCT ls ∧
  ssa_map_ok na ssaL
  ⇒
  let(moveL,moveR,na',ssaL',ssaR') = fake_moves prio ls ssaL ssaR na in
  (ssa_locals_rel na ssaL stL.locals cstL.locals ⇒
  let (resL,rcstL) = evaluate(moveL,cstL) in
    resL = NONE ∧
    (∀x. ¬MEM x ls ⇒ lookup x ssaL' = lookup x ssaL) ∧
    (∀x y. (x < na ∧ lookup x cstL.locals = SOME y)
    ⇒  lookup x rcstL.locals = SOME y) ∧
    ssa_locals_rel na' ssaL' stL.locals rcstL.locals ∧
    word_state_eq_rel cstL rcstL)``,
  Induct>>full_simp_tac(srw_ss())[fake_moves_def]>-
    (srw_tac[][]>>
    full_simp_tac(srw_ss())[evaluate_def,word_state_eq_rel_def,get_vars_def,set_vars_def,alist_insert_def]>>
    rev_full_simp_tac(srw_ss())[]>>srw_tac[][])>>
  rpt strip_tac>>
  first_x_assum(qspecl_then[`na`,`ssaL`,`ssaR`,`stL`,`cstL`]mp_tac)>>
  impl_tac>-
    (rev_full_simp_tac(srw_ss())[LET_THM]>>
    metis_tac[])>>
  strip_tac>>
  rev_full_simp_tac(srw_ss())[LET_THM]>>
  Cases_on`fake_moves prio ls ssaL ssaR na`>>PairCases_on`r`>>full_simp_tac(srw_ss())[]>>
  EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
  strip_tac>>full_simp_tac(srw_ss())[]>>
  full_simp_tac(srw_ss())[evaluate_def,LET_THM,evaluate_def,fake_move_def,word_exp_def,inst_def,assign_def]>>
  Cases_on`evaluate(q,cstL)`>>full_simp_tac(srw_ss())[]>>
  `na ≤ r1 ∧ ssa_map_ok r1 r2` by
    (imp_res_tac fake_moves_frame>>
    full_simp_tac(srw_ss())[LET_THM]>>
    pop_assum(qspecl_then[`ssaR`,`ssaL`,`prio`,`ls`]assume_tac)>>rev_full_simp_tac(srw_ss())[])
  >-
    (full_simp_tac(srw_ss())[ssa_locals_rel_def]>>
    res_tac>>
    full_simp_tac(srw_ss())[domain_lookup,get_vars_def,get_var_def,set_vars_def,alist_insert_def]>>
    srw_tac[][]>>full_simp_tac(srw_ss())[lookup_insert]
    >-
      (`x' ≠ r1` by DECIDE_TAC>>
      full_simp_tac(srw_ss())[lookup_insert])
    >-
      (IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
      Cases_on`x'=h`>>full_simp_tac(srw_ss())[]>>
      metis_tac[])
    >-
      (Cases_on`x'=h`>>full_simp_tac(srw_ss())[]>-
      (res_tac>>full_simp_tac(srw_ss())[]>>
      qpat_x_assum`lookup h r2 = SOME v'''` SUBST_ALL_TAC>>
      full_simp_tac(srw_ss())[]>>
      rev_full_simp_tac(srw_ss())[])
      >>
      res_tac>>full_simp_tac(srw_ss())[]>>
      `v''' < r1` by
        (full_simp_tac(srw_ss())[ssa_map_ok_def]>>
        metis_tac[])>>
      `v''' ≠ r1` by DECIDE_TAC>>
      full_simp_tac(srw_ss())[])
    >-
      (res_tac>>
      DECIDE_TAC)
    >>
      full_simp_tac(srw_ss())[word_state_eq_rel_def])
  >-
    (full_simp_tac(srw_ss())[ssa_locals_rel_def]>>
    res_tac>>
    full_simp_tac(srw_ss())[domain_lookup,set_var_def]>>
    srw_tac[][]>>full_simp_tac(srw_ss())[lookup_insert]
    >-
      (`x' ≠ r1` by DECIDE_TAC>>
      full_simp_tac(srw_ss())[lookup_insert])
    >-
      (IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
      Cases_on`x'=h`>>full_simp_tac(srw_ss())[]>>
      metis_tac[])
    >-
      (Cases_on`x'=h`>>full_simp_tac(srw_ss())[]>-
        (res_tac>>full_simp_tac(srw_ss())[])
      >>
      res_tac>>full_simp_tac(srw_ss())[]>>
      `v' < r1` by
        (full_simp_tac(srw_ss())[ssa_map_ok_def]>>
        metis_tac[])>>
      `v' ≠ r1` by DECIDE_TAC>>
      full_simp_tac(srw_ss())[])
    >-
      (res_tac>>
      DECIDE_TAC)
    >>
      full_simp_tac(srw_ss())[word_state_eq_rel_def]));

val fix_inconsistencies_correctL = prove (``  ∀na ssaL ssaR.
  is_alloc_var na ∧
  ssa_map_ok na ssaL
  ⇒
  let(moveL,moveR,na',ssaU) = fix_inconsistencies prio ssaL ssaR na in
  (∀(stL:('a,'b,'c) wordSem$state) (cstL:('a,'b,'c) wordSem$state).
  ssa_locals_rel na ssaL stL.locals cstL.locals ⇒
  let (resL,rcstL) = evaluate(moveL,cstL) in
    resL = NONE ∧
    ssa_locals_rel na' ssaU stL.locals rcstL.locals ∧
    word_state_eq_rel cstL rcstL)``,
  full_simp_tac(srw_ss())[fix_inconsistencies_def]>>LET_ELIM_TAC>>
  rename1`Move pp`>>
  Q.ISPECL_THEN [`var_union`,`na`,`ssaL`,`ssaR`,`stL`,`cstL`,`pp`] mp_tac
      merge_moves_correctL>>
  full_simp_tac(srw_ss())[]>>
  (impl_keep_tac>-
    (full_simp_tac(srw_ss())[Abbr`var_union`,ALL_DISTINCT_MAP_FST_toAList]))>>
  LET_ELIM_TAC>>
  Q.ISPECL_THEN [`var_union`,`na'`,`ssaL'`,`ssaR'`,`stL`,`rcstL'`]mp_tac
      fake_moves_correctL>>
  (impl_tac>-
      (Q.ISPECL_THEN [`var_union`,`na`,`ssaL`,`ssaR`] assume_tac merge_moves_frame>>rev_full_simp_tac(srw_ss())[LET_THM]))>>
  LET_ELIM_TAC>>
  rev_full_simp_tac(srw_ss())[]>>
  qpat_x_assum`A=moveL` sym_sub_tac>>
  qpat_x_assum`A=(resL,B)` mp_tac>>
  simp[Once evaluate_def]>>
  full_simp_tac(srw_ss())[]>>
  rpt VAR_EQ_TAC>>full_simp_tac(srw_ss())[]>>
  srw_tac[][]>>full_simp_tac(srw_ss())[word_state_eq_rel_def]);
val result = fix_inconsistencies_correctL;
val merge_moves_correctR = GEN_ALL (prove (``∀ls na ssaL ssaR stR cstR pri.
  is_alloc_var na ∧
  ALL_DISTINCT ls ∧
  ssa_map_ok na ssaR
  ⇒
  let(moveL,moveR,na',ssaL',ssaR') = merge_moves ls ssaL ssaR na in
  (ssa_locals_rel na ssaR stR.locals cstR.locals ⇒
  let (resR,rcstR) = evaluate(Move pri moveR,cstR) in
    resR = NONE ∧
    (∀x. ¬MEM x ls ⇒ lookup x ssaR' = lookup x ssaR) ∧
    (∀x y. (x < na ∧ lookup x cstR.locals = SOME y)
    ⇒  lookup x rcstR.locals = SOME y) ∧
    ssa_locals_rel na' ssaR' stR.locals rcstR.locals ∧
    word_state_eq_rel cstR rcstR)``,
  Induct>>full_simp_tac(srw_ss())[merge_moves_def]>-
  (srw_tac[][]>>
  full_simp_tac(srw_ss())[evaluate_def,word_state_eq_rel_def,get_vars_def,set_vars_def,alist_insert_def]>>
  rev_full_simp_tac(srw_ss())[]>>srw_tac[][])>>
  rpt strip_tac>>
  first_x_assum(qspecl_then[`na`,`ssaL`,`ssaR`,`stR`,`cstR`,`pri`]mp_tac)>>
  impl_tac>-
    (rev_full_simp_tac(srw_ss())[LET_THM]>>
    metis_tac[])>>
  strip_tac>>
  rev_full_simp_tac(srw_ss())[LET_THM]>>
  Cases_on`merge_moves ls ssaL ssaR na`>>PairCases_on`r`>>full_simp_tac(srw_ss())[]>>
  EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
  strip_tac>>full_simp_tac(srw_ss())[]>>
  Cases_on`evaluate(Move pri r0,cstR)`>>full_simp_tac(srw_ss())[]>>
  imp_res_tac merge_moves_frame>>
  pop_assum(qspecl_then[`ssaR`,`ssaL`,`ls`]assume_tac)>>
  Q.ISPECL_THEN [`ls`,`na`,`ssaL`,`ssaR`] assume_tac merge_moves_fst>>
  rev_full_simp_tac(srw_ss())[LET_THM]>>
  imp_res_tac mov_eval_head>>
  pop_assum(qspec_then`r1` mp_tac)>>impl_tac>-
    (SPOSE_NOT_THEN assume_tac>>full_simp_tac(srw_ss())[EVERY_MEM]>>
    res_tac>>
    DECIDE_TAC)>>
  strip_tac>>
  pop_assum(qspec_then`x` mp_tac)>>impl_tac>-
    (SPOSE_NOT_THEN assume_tac>>full_simp_tac(srw_ss())[EVERY_MEM,ssa_map_ok_def]>>
    res_tac>>
    DECIDE_TAC)>>
  impl_tac>-
    (full_simp_tac(srw_ss())[ssa_locals_rel_def]>>
    metis_tac[])>>
  strip_tac>>
  srw_tac[][]>>full_simp_tac(srw_ss())[lookup_insert]
  >-
    (`x'' ≠ r1` by DECIDE_TAC>>
    full_simp_tac(srw_ss())[lookup_insert])
  >-
    (full_simp_tac(srw_ss())[ssa_locals_rel_def]>>
    srw_tac[][]>>full_simp_tac(srw_ss())[lookup_insert]
    >-
      (Cases_on`x''=h`>>full_simp_tac(srw_ss())[]>>
      metis_tac[])
    >-
      (Cases_on`x''=h`>>full_simp_tac(srw_ss())[]>-
      (res_tac>>full_simp_tac(srw_ss())[]>>
      qpat_x_assum`lookup h ssaR = SOME x` (SUBST_ALL_TAC)>>
      full_simp_tac(srw_ss())[])>>
      res_tac>>
      full_simp_tac(srw_ss())[domain_lookup]>>
       `v'' < r1` by
        (full_simp_tac(srw_ss())[ssa_map_ok_def]>>
        metis_tac[])>>
      `v'' ≠ r1` by DECIDE_TAC>>
      full_simp_tac(srw_ss())[])
    >-
      (res_tac>>DECIDE_TAC))
  >>
      full_simp_tac(srw_ss())[word_state_eq_rel_def]));

val fake_moves_correctR = prove (``  ∀ls na ssaL ssaR stR cstR.
  is_alloc_var na ∧
  ALL_DISTINCT ls ∧
  ssa_map_ok na ssaR
  ⇒
  let(moveL,moveR,na',ssaL',ssaR') = fake_moves prio ls ssaL ssaR na in
  (ssa_locals_rel na ssaR stR.locals cstR.locals ⇒
  let (resR,rcstR) = evaluate(moveR,cstR) in
    resR = NONE ∧
    (∀x. ¬MEM x ls ⇒ lookup x ssaR' = lookup x ssaR) ∧
    (∀x y. (x < na ∧ lookup x cstR.locals = SOME y)
    ⇒  lookup x rcstR.locals = SOME y) ∧
    ssa_locals_rel na' ssaR' stR.locals rcstR.locals ∧
    word_state_eq_rel cstR rcstR)``,
  Induct>>full_simp_tac(srw_ss())[fake_moves_def]>-
  (srw_tac[][]>>
  full_simp_tac(srw_ss())[evaluate_def,word_state_eq_rel_def,get_vars_def,set_vars_def,alist_insert_def]>>
  rev_full_simp_tac(srw_ss())[]>>srw_tac[][])>>
  rpt strip_tac>>
  first_x_assum(qspecl_then[`na`,`ssaL`,`ssaR`,`stR`,`cstR`]mp_tac)>>
  impl_tac>-
    (rev_full_simp_tac(srw_ss())[LET_THM]>>
    metis_tac[])>>
  strip_tac>>
  rev_full_simp_tac(srw_ss())[LET_THM]>>
  Cases_on`fake_moves prio ls ssaL ssaR na`>>PairCases_on`r`>>full_simp_tac(srw_ss())[]>>
  EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
  strip_tac>>full_simp_tac(srw_ss())[]>>
  full_simp_tac(srw_ss())[evaluate_def,LET_THM,evaluate_def,fake_move_def,word_exp_def,inst_def,assign_def]>>
  Cases_on`evaluate(r0,cstR)`>>full_simp_tac(srw_ss())[]>>
  `na ≤ r1 ∧ ssa_map_ok r1 r3` by
    (imp_res_tac fake_moves_frame>>
    full_simp_tac(srw_ss())[LET_THM]>>
    pop_assum(qspecl_then[`ssaR`,`ssaL`,`prio`,`ls`]assume_tac)>>rev_full_simp_tac(srw_ss())[])
  >-
    (full_simp_tac(srw_ss())[ssa_locals_rel_def]>>
    res_tac>>
    full_simp_tac(srw_ss())[domain_lookup,set_var_def]>>
    srw_tac[][]>>full_simp_tac(srw_ss())[lookup_insert]
    >-
      (`x' ≠ r1` by DECIDE_TAC>>
      full_simp_tac(srw_ss())[lookup_insert])
    >-
      (IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
      Cases_on`x'=h`>>full_simp_tac(srw_ss())[]>>
      metis_tac[])
    >-
      (Cases_on`x'=h`>>full_simp_tac(srw_ss())[]>-
        (res_tac>>full_simp_tac(srw_ss())[])
      >>
      res_tac>>full_simp_tac(srw_ss())[]>>
      `v' < r1` by
        (full_simp_tac(srw_ss())[ssa_map_ok_def]>>
        metis_tac[])>>
      `v' ≠ r1` by DECIDE_TAC>>
      full_simp_tac(srw_ss())[])
    >-
      (res_tac>>
      DECIDE_TAC)
    >>
      full_simp_tac(srw_ss())[word_state_eq_rel_def])
  >-
    (full_simp_tac(srw_ss())[ssa_locals_rel_def]>>
    res_tac>>
    full_simp_tac(srw_ss())[domain_lookup,get_vars_def,get_var_def,set_vars_def,alist_insert_def]>>
    srw_tac[][]>>full_simp_tac(srw_ss())[lookup_insert]
    >-
      (`x' ≠ r1` by DECIDE_TAC>>
      full_simp_tac(srw_ss())[lookup_insert])
    >-
      (IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
      Cases_on`x'=h`>>full_simp_tac(srw_ss())[]>>
      metis_tac[])
    >-
      (Cases_on`x'=h`>>full_simp_tac(srw_ss())[]>-
      (res_tac>>full_simp_tac(srw_ss())[]>>
      qpat_x_assum`lookup h r3 = SOME v'''` SUBST_ALL_TAC>>
      full_simp_tac(srw_ss())[]>>
      rev_full_simp_tac(srw_ss())[])
      >>
      res_tac>>full_simp_tac(srw_ss())[]>>
      `v''' < r1` by
        (full_simp_tac(srw_ss())[ssa_map_ok_def]>>
        metis_tac[])>>
      `v''' ≠ r1` by DECIDE_TAC>>
      full_simp_tac(srw_ss())[])
    >-
      (res_tac>>
      DECIDE_TAC)
    >>
      full_simp_tac(srw_ss())[word_state_eq_rel_def]));

val merge_moves_frame2 = prove (``  ∀ls na ssaL ssaR.
  let(moveL,moveR,na',ssaL',ssaR') = merge_moves ls ssaL ssaR na in
  domain ssaL' = domain ssaL ∧
  domain ssaR' = domain ssaR ∧
  ∀x. MEM x ls ∧ x ∈ domain (inter ssaL ssaR) ⇒
    lookup x ssaL' = lookup x ssaR'``,
  Induct>>full_simp_tac(srw_ss())[merge_moves_def]>-
    (srw_tac[][]>>full_simp_tac(srw_ss())[])
  >>
  rpt strip_tac>>
  full_simp_tac(srw_ss())[LET_THM]>>
  last_x_assum(qspecl_then[`na`,`ssaL`,`ssaR`] assume_tac)>>
  rev_full_simp_tac(srw_ss())[LET_THM]>>
  Cases_on`merge_moves ls ssaL ssaR na`>>PairCases_on`r`>>rev_full_simp_tac(srw_ss())[]>>
  EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]
  >-
    metis_tac[]
  >> TRY
    (full_simp_tac(srw_ss())[domain_inter]>>srw_tac[][]>>
    qpat_x_assum`A=domain ssaL` (sym_sub_tac)>>
    qpat_x_assum`A=domain ssaR` (sym_sub_tac)>>
    full_simp_tac(srw_ss())[domain_lookup]>>
    full_simp_tac(srw_ss())[optionTheory.SOME_11]>>
    res_tac>>
    rev_full_simp_tac(srw_ss())[])
  >>
    full_simp_tac(srw_ss())[EXTENSION]>>srw_tac[][]>>
    metis_tac[domain_lookup,lookup_insert]);
val merge_moves_frame3 = prove (``  ∀ls na ssaL ssaR.
  let(moveL,moveR,na',ssaL',ssaR') = merge_moves ls ssaL ssaR na in
  ∀x. ¬MEM x ls ∨ x ∉ domain (inter ssaL ssaR) ⇒
    lookup x ssaL' = lookup x ssaL ∧
    lookup x ssaR' = lookup x ssaR``,
  Induct>>full_simp_tac(srw_ss())[merge_moves_def]>-
    (srw_tac[][]>>full_simp_tac(srw_ss())[])>>
  rpt strip_tac>>
  full_simp_tac(srw_ss())[LET_THM]>>
  last_x_assum(qspecl_then[`na`,`ssaL`,`ssaR`] assume_tac)>>
  rev_full_simp_tac(srw_ss())[LET_THM]>>
  Cases_on`merge_moves ls ssaL ssaR na`>>PairCases_on`r`>>rev_full_simp_tac(srw_ss())[]>>
  EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
  TRY(metis_tac[])>>
  srw_tac[][]>>full_simp_tac(srw_ss())[lookup_insert]>>
  IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
  Q.ISPECL_THEN [`ls`,`na`,`ssaL`,`ssaR`] assume_tac merge_moves_frame2>>
  rev_full_simp_tac(srw_ss())[LET_THM]>>
  `h ∈ domain r3 ∧ h ∈ domain r2` by full_simp_tac(srw_ss())[domain_lookup]>>
  full_simp_tac(srw_ss())[domain_inter]>>
  metis_tac[]);
val fake_moves_frame2 = prove (``  ∀ls na ssaL ssaR.
  let(moveL,moveR,na',ssaL',ssaR') = fake_moves prio ls ssaL ssaR na in
  domain ssaL' = domain ssaL ∪ (set ls ∩ (domain ssaR ∪ domain ssaL)) ∧
  domain ssaR' = domain ssaR ∪ (set ls ∩ (domain ssaR ∪ domain ssaL)) ∧
  ∀x. MEM x ls ∧ x ∉ domain(inter ssaL ssaR) ⇒ lookup x ssaL' = lookup x ssaR'``,
  Induct>>full_simp_tac(srw_ss())[fake_moves_def]>-
    (srw_tac[][]>>full_simp_tac(srw_ss())[])
  >>
  rpt strip_tac>>
  full_simp_tac(srw_ss())[LET_THM]>>
  last_x_assum(qspecl_then[`na`,`ssaL`,`ssaR`] assume_tac)>>
  rev_full_simp_tac(srw_ss())[LET_THM]>>
  Cases_on`fake_moves prio ls ssaL ssaR na`>>PairCases_on`r`>>rev_full_simp_tac(srw_ss())[]>>
  EVERY_CASE_TAC>>
  full_simp_tac(srw_ss())[EXTENSION,domain_inter]>>srw_tac[][]>>
  metis_tac[domain_lookup,lookup_insert]);
val fake_moves_frame3 = prove (``  ∀ls na ssaL ssaR.
  let(moveL,moveR,na',ssaL',ssaR') = fake_moves prio ls ssaL ssaR na in
  ∀x. ¬ MEM x ls ∨ x ∈ domain(inter ssaL ssaR) ⇒
    lookup x ssaL' = lookup x ssaL ∧
    lookup x ssaR' = lookup x ssaR``,
  Induct>>full_simp_tac(srw_ss())[fake_moves_def]>-
    (srw_tac[][]>>full_simp_tac(srw_ss())[])
  >>
  rpt strip_tac>>
  full_simp_tac(srw_ss())[LET_THM]>>
  last_x_assum(qspecl_then[`na`,`ssaL`,`ssaR`] assume_tac)>>
  rev_full_simp_tac(srw_ss())[LET_THM]>>
  Cases_on`fake_moves prio ls ssaL ssaR na`>>PairCases_on`r`>>rev_full_simp_tac(srw_ss())[]>>
  Q.ISPECL_THEN[`ls`,`na`,`ssaL`,`ssaR`] assume_tac fake_moves_frame2>>
  rev_full_simp_tac(srw_ss())[LET_THM]>>
  EVERY_CASE_TAC>>
  full_simp_tac(srw_ss())[EXTENSION,domain_inter]>>srw_tac[][]>>
  full_simp_tac(srw_ss())[lookup_insert]>>
  IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
  `h ∈ domain r2` by full_simp_tac(srw_ss())[domain_lookup]>>
  res_tac>>
  full_simp_tac(srw_ss())[lookup_NONE_domain]);
val ssa_eq_rel_swap = prove (``  ssa_locals_rel na ssaR st.locals cst.locals ∧
  domain ssaL = domain ssaR ∧
  (∀x. lookup x ssaL = lookup x ssaR) ⇒
  ssa_locals_rel na ssaL st.locals cst.locals``,
  srw_tac[][ssa_locals_rel_def]);
val fix_inconsistencies_correctR = prove (``  ∀na ssaL ssaR prio.
  is_alloc_var na ∧
  ssa_map_ok na ssaR
  ⇒
  let(moveL,moveR,na',ssaU) = fix_inconsistencies prio ssaL ssaR na in
  (∀(stR:('a,'b,'c) wordSem$state) (cstR:('a,'b,'c) wordSem$state).
  ssa_locals_rel na ssaR stR.locals cstR.locals ⇒
  let (resR,rcstR) = evaluate(moveR,cstR) in
    resR = NONE ∧
    ssa_locals_rel na' ssaU stR.locals rcstR.locals ∧
    word_state_eq_rel cstR rcstR)``,
  full_simp_tac(srw_ss())[fix_inconsistencies_def]>>LET_ELIM_TAC>>
  rename1`Move ppl Lmov`>>
  rename1`Move ppr Rmov`>>
  Q.ISPECL_THEN [`var_union`,`na`,`ssaL`,`ssaR`,`stR`,`cstR`,`ppr`] mp_tac merge_moves_correctR>>
  full_simp_tac(srw_ss())[]>>
  (impl_keep_tac>-
    (full_simp_tac(srw_ss())[Abbr`var_union`,ALL_DISTINCT_MAP_FST_toAList]))>>
  LET_ELIM_TAC>>
  Q.ISPECL_THEN [`var_union`,`na'`,`ssaL'`,`ssaR'`,`stR`,`rcstR'`]mp_tac fake_moves_correctR>>
  (impl_tac>-
      (Q.ISPECL_THEN [`var_union`,`na`,`ssaL`,`ssaR`] assume_tac merge_moves_frame>>rev_full_simp_tac(srw_ss())[LET_THM]))>>
  LET_ELIM_TAC>>
  rev_full_simp_tac(srw_ss())[]>>
  qpat_x_assum`A=moveR` sym_sub_tac>>
  qpat_x_assum`A=(resR,B)` mp_tac>>
  simp[Once evaluate_def]>>
  full_simp_tac(srw_ss())[]>>
  rpt VAR_EQ_TAC>>full_simp_tac(srw_ss())[]>>
  srw_tac[][]>>full_simp_tac(srw_ss())[word_state_eq_rel_def]>>
  Q.ISPECL_THEN[`var_union`,`na`,`ssaL`,`ssaR`] assume_tac
    merge_moves_frame2>>
  Q.ISPECL_THEN[`var_union`,`na'`,`ssaL'`,`ssaR'`] assume_tac
    fake_moves_frame2>>
  Q.ISPECL_THEN[`var_union`,`na`,`ssaL`,`ssaR`] assume_tac
    merge_moves_frame3>>
  Q.ISPECL_THEN[`var_union`,`na'`,`ssaL'`,`ssaR'`] assume_tac
    fake_moves_frame3>>
  rev_full_simp_tac(srw_ss())[LET_THM]>>
  match_mp_tac (GEN_ALL ssa_eq_rel_swap)>>
  HINT_EXISTS_TAC>>rev_full_simp_tac(srw_ss())[]>>
  full_simp_tac(srw_ss())[Abbr`var_union`,EXTENSION]>>CONJ_ASM1_TAC>-
    (full_simp_tac(srw_ss())[toAList_domain,domain_union]>>
    metis_tac[])>>
  full_simp_tac(srw_ss())[toAList_domain]>>srw_tac[][]>>
  reverse(Cases_on`x ∈ domain (union ssaL ssaR)`)
  >-
    (full_simp_tac(srw_ss())[domain_union]>>
    metis_tac[lookup_NONE_domain])
  >>
    full_simp_tac(srw_ss())[domain_inter]>>
    metis_tac[]);
val first_statement = Q.SPEC `p` ssa_cc_trans_correct;
val second_statement = Q.SPEC `p0` ssa_cc_trans_correct;
val outer_statement = Q.SPEC `If c n r p p0` ssa_cc_trans_correct;
val recursive_statement = mk_imp(concl first_statement, mk_imp(concl second_statement, concl outer_statement));
val recursive_case = prove(recursive_statement, rpt strip_tac >>
    qpat_abbrev_tac `A = ssa_cc_trans B C D E` >>
    PairCases_on`A`>>simp[]>>
    pop_assum(mp_tac o SYM o SIMP_RULE std_ss[markerTheory.Abbrev_def]) >>
    full_simp_tac(srw_ss())[evaluate_def,ssa_cc_trans_def]>>
    LET_ELIM_TAC>>fs[]>>
    qpat_x_assum`B = A0` sym_sub_tac>>full_simp_tac(srw_ss())[evaluate_def]>>
    Cases_on `get_var n st` >> gvs [] >>
    Cases_on `get_var_imm r st` >> gvs [] >>
    imp_res_tac ssa_locals_rel_get_var >> gvs [Abbr `r1'`] >>
    `get_var_imm ri' cst = SOME x'` by (
      Cases_on `r` >> gvs [Abbr `ri'`, get_var_imm_def] >>
      metis_tac [ssa_locals_rel_get_var]) >>
    gvs [] >>
    Cases_on `word_cmp c x x'` >> gvs [] >>
    Cases_on `x''` >> gvs []
    >- (
      qpat_x_assum `∀st cst ssa na lt. word_state_eq_rel st cst ∧ _ ∧ is_alloc_var na ∧ every_var _ p ∧ _ ⇒ _` (qspecl_then[`st`,`cst`,`ssa`,`na`,`lt`] mp_tac)>>
      impl_tac>-
        (rev_full_simp_tac(srw_ss())[]>>imp_res_tac ssa_cc_trans_props>>
        full_simp_tac(srw_ss())[every_var_def])>>
      srw_tac[][]>>
      qexists_tac`perm'`>>full_simp_tac(srw_ss())[LET_THM]>>
      Cases_on`evaluate(p,st with permute := perm')`>>
      Cases_on`evaluate(e2',cst)`>>full_simp_tac(srw_ss())[]>>
      gvs[] >>
      Cases_on`q`>>full_simp_tac(srw_ss())[]>>rev_full_simp_tac(srw_ss())[]>>
      Q.SPECL_THEN [`na3`,`ssa2`,`ssa3`] mp_tac fix_inconsistencies_correctL>>
      impl_tac>-
        (imp_res_tac ssa_cc_trans_props>>
        metis_tac[ssa_map_ok_more])>>
      rev_full_simp_tac(srw_ss())[LET_THM]>>
      disch_then (qspecl_then[`r'`,`r''`] mp_tac)>>
      impl_tac>-
        (imp_res_tac ssa_cc_trans_props>>
        metis_tac[ssa_locals_rel_more,ssa_map_ok_more])>>
      Cases_on`evaluate(e2_cons,r'')`>>full_simp_tac(srw_ss())[word_state_eq_rel_def])
    >>
      qpat_x_assum `∀st cst ssa na lt. word_state_eq_rel st cst ∧ _ ∧ is_alloc_var na ∧ every_var _ p0 ∧ _ ⇒ _` (qspecl_then[`st`,`cst`,`ssa`,`na2`,`lt`] mp_tac)>>
      impl_tac>-
        (rev_full_simp_tac(srw_ss())[]>>imp_res_tac ssa_cc_trans_props>>srw_tac[][]
        >-
          metis_tac[ssa_locals_rel_more]
        >-
          (full_simp_tac(srw_ss())[every_var_def]>>match_mp_tac every_var_mono>>
          Q.EXISTS_TAC`λx.x<na`>>full_simp_tac(srw_ss())[] >>
          DECIDE_TAC)
        >>
          metis_tac[ssa_map_ok_more])
      >>
      srw_tac[][]>>
      qexists_tac`perm'`>>full_simp_tac(srw_ss())[LET_THM]>>
      Cases_on`evaluate(p0,st with permute := perm')`>>
      Cases_on`evaluate(e3',cst)`>>full_simp_tac(srw_ss())[]>>
      Cases_on`q'`>>full_simp_tac(srw_ss())[]>>rev_full_simp_tac(srw_ss())[]>>
      rename1`fix_inconsistencies prio _ _`>>
      Q.SPECL_THEN [`na3`,`ssa2`,`ssa3`,`prio`] mp_tac fix_inconsistencies_correctR>>
      impl_tac>-
        (imp_res_tac ssa_cc_trans_props>>
        metis_tac[ssa_map_ok_more])>>
      rev_full_simp_tac(srw_ss())[LET_THM]>>srw_tac[][]>>
      pop_assum (qspecl_then[`r'`,`r''`] mp_tac)>>
      impl_tac>-
        (imp_res_tac ssa_cc_trans_props>>
        metis_tac[ssa_locals_rel_more,ssa_map_ok_more])>>
      Cases_on`evaluate(e3_cons,r'')`>>full_simp_tac(srw_ss())[word_state_eq_rel_def]);
fun out label th = (print(label ^ "="); print_thm th; print "\n");
val _ = out "if_recursive_full" recursive_case;
val _ = out "if_original_full" outer_statement;
fun ty label name th = let val v=valOf(List.find(fn t => fst(dest_var t)=name)(free_vars(concl(SPEC_ALL th)))) in print(label ^ "="); print_type(type_of v); print "\n" end;
val _ = ty "if_type_st" "st" outer_statement;
val _ = ty "if_type_cst" "cst" outer_statement;
val _ = ty "if_type_first" "p" outer_statement;
val _ = ty "if_type_second" "p0" outer_statement;
val _ = ty "if_type_ssa" "ssa" outer_statement;
val _ = ty "if_type_na" "na" outer_statement;
val _ = ty "if_type_lt" "lt" outer_statement;
val _ = ty "if_type_cmp" "c" outer_statement;
val _ = ty "if_type_reg" "n" outer_statement;
val _ = ty "if_type_imm" "r" outer_statement;
