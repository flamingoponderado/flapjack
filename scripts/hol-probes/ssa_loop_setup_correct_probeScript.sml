load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory word_allocTheory wordSemTheory wordLangTheory sptreeTheory reg_allocTheory;
val _ = Globals.linewidth := 1000;
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
fun out label th = (print(label ^ "="); print_thm th; print "\n");
fun ty label name th = let val v=valOf(List.find(fn t => fst(dest_var t)=name)(free_vars(concl(SPEC_ALL th)))) in print(label ^ "="); print_type(type_of v); print "\n" end;
val _ = out "loop_setup_full" loop_setup_correct;
val _ = ty "loop_setup_type_st" "st" loop_setup_correct;
val _ = ty "loop_setup_type_cst" "cst" loop_setup_correct;
val _ = ty "loop_setup_type_ssa" "ssa" loop_setup_correct;
val _ = ty "loop_setup_type_na" "na" loop_setup_correct;
val _ = ty "loop_setup_type_names" "names" loop_setup_correct;
val _ = ty "loop_setup_type_exit_names" "exit_names" loop_setup_correct;
val _ = ty "loop_setup_type_setup_prog" "setup_prog" loop_setup_correct;
val _ = ty "loop_setup_type_ssa_refreshed" "ssa_refreshed" loop_setup_correct;
val _ = ty "loop_setup_type_na_refreshed" "na_refreshed" loop_setup_correct;
