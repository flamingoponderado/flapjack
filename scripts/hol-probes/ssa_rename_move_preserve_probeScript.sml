load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory word_allocTheory wordSemTheory sptreeTheory;
val _ = Globals.linewidth := 1000;
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
open reg_allocTheory;
val ssa_locals_rel_get_var = prove (``  ssa_locals_rel na ssa st.locals cst.locals ∧
  get_var n st = SOME x
  ⇒
  get_var (option_lookup ssa n) cst = SOME x``,
  full_simp_tac(srw_ss())[get_var_def,ssa_locals_rel_def,strong_locals_rel_def,option_lookup_def]>>
  srw_tac[][]>>
  FULL_CASE_TAC>>full_simp_tac(srw_ss())[domain_lookup]>>
  first_x_assum(qspecl_then[`n`,`x`] assume_tac)>>rev_full_simp_tac(srw_ss())[]);
val ssa_locals_rel_get_vars = prove (``  ∀ls y na ssa st cst.
  ssa_locals_rel na ssa st.locals cst.locals ∧
  get_vars ls st = SOME y
  ⇒
  get_vars (MAP (option_lookup ssa) ls) cst = SOME y``,
  Induct>>full_simp_tac(srw_ss())[get_vars_def]>>srw_tac[][]>>
  Cases_on`get_var h st`>>full_simp_tac(srw_ss())[]>>
  imp_res_tac ssa_locals_rel_get_var>>full_simp_tac(srw_ss())[]>>
  Cases_on`get_vars ls st`>>full_simp_tac(srw_ss())[]>>
  res_tac>>full_simp_tac(srw_ss())[]);
fun use_ALOOKUP_ALL_DISTINCT_MEM (g as (asl,w)) =
  let
    val tm = find_term(can(match_term(lhs(snd(dest_imp(concl
      ALOOKUP_ALL_DISTINCT_MEM)))))) w
    val (_,[al,k]) = strip_comb tm
  in
    mp_tac(ISPECL [al,k] (Q.GENL[`al`,`k`,`v`] ALOOKUP_ALL_DISTINCT_MEM))
  end g;


val list_next_var_rename_move_preserve = prove (``  ∀st ssa na ls cst.
  ssa_locals_rel na ssa st.locals cst.locals ∧
  set ls ⊆ domain st.locals ∧
  ALL_DISTINCT ls ∧
  ssa_map_ok na ssa ∧
  word_state_eq_rel st cst
  ⇒
  let (mov,ssa',na') = list_next_var_rename_move ssa na ls in
  let (res,rcst) = evaluate (mov,cst) in
    res = NONE ∧
    ssa_locals_rel na' ssa' st.locals rcst.locals ∧
    word_state_eq_rel st rcst ∧
    (¬is_phy_var na ⇒ ∀w. is_phy_var w ⇒ lookup w rcst.locals = lookup w cst.locals) ∧
    (∀x y. lookup x st.locals = SOME y ⇒ lookup (THE (lookup x ssa)) rcst.locals = SOME y)``,
    full_simp_tac(srw_ss())[list_next_var_rename_move_def,ssa_locals_rel_def]>>
  srw_tac[][]>>
  imp_res_tac list_next_var_rename_lemma_1>>
  imp_res_tac list_next_var_rename_lemma_2>>
  first_x_assum(qspecl_then[`ssa`,`na`] assume_tac)>>
  full_simp_tac(srw_ss())[LET_THM,evaluate_def]>>rev_full_simp_tac(srw_ss())[]>>
  rev_full_simp_tac(srw_ss())[MAP_ZIP,LENGTH_COUNT_LIST,Abbr`cur_ls`]>>full_simp_tac(srw_ss())[]>>
  imp_res_tac get_vars_eq>>
  qpat_x_assum`A=(res,rcst)` mp_tac>>
  qabbrev_tac`v=get_vars ls st`>>
  qpat_abbrev_tac`cls = MAP (option_lookup ssa) ls`>>
  `get_vars cls cst = v` by
    (full_simp_tac(srw_ss())[Abbr`cls`]>>
    match_mp_tac ssa_locals_rel_get_vars>>
    full_simp_tac(srw_ss())[ssa_locals_rel_def]>>
    qexists_tac`na`>>
    qexists_tac`st`>>full_simp_tac(srw_ss())[]>>
    metis_tac[])>>
  full_simp_tac(srw_ss())[Abbr`v`]>>srw_tac[][]
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
      (res_tac>>
      use_ALOOKUP_ALL_DISTINCT_MEM >>
      simp[ZIP_MAP,MAP_MAP_o,combinTheory.o_DEF,MEM_MAP,PULL_EXISTS] >>
      strip_tac>>
      pop_assum(qspec_then`x` assume_tac)>>
      rev_full_simp_tac(srw_ss())[])
    >>
      (full_simp_tac(srw_ss())[domain_lookup]>>
      qpat_abbrev_tac `opt:'a word_loc option = ALOOKUP (ZIP A) v`>>
      qsuff_tac `opt = NONE` >>full_simp_tac(srw_ss())[Abbr`opt`]>>
      match_mp_tac (SPEC_ALL ALOOKUP_NONE|>REWRITE_RULE[EQ_IMP_THM]|>CONJ_PAIR|>snd)>>
      SPOSE_NOT_THEN assume_tac>>
      full_simp_tac(srw_ss())[MAP_ZIP]>>
      full_simp_tac(srw_ss())[domain_lookup]>>
      `v < na` by
        metis_tac[ssa_map_ok_def]>>
      rev_full_simp_tac(srw_ss())[]>>
      rpt (qpat_x_assum`A = B` sym_sub_tac)>>
      full_simp_tac(srw_ss())[MEM_MAP]>>DECIDE_TAC))
  >-
    (res_tac>>DECIDE_TAC)
  >-
    full_simp_tac(srw_ss())[word_state_eq_rel_def,set_vars_def]
  >-
    (full_simp_tac(srw_ss())[lookup_alist_insert,set_vars_def]>>
    FULL_CASE_TAC>>
    imp_res_tac ALOOKUP_MEM>>
    full_simp_tac(srw_ss())[MEM_ZIP]>>
    qpat_x_assum`MAP A B = MAP C D` sym_sub_tac>>
    rev_full_simp_tac(srw_ss())[EL_MAP,LENGTH_MAP,LENGTH_COUNT_LIST,EL_COUNT_LIST]>>
    `is_stack_var na ∨ is_alloc_var na` by
      metis_tac[convention_partitions]>>
    `is_stack_var w ∨ is_alloc_var w` by
      (mp_tac arithmeticTheory.MOD_PLUS >>
      full_simp_tac(srw_ss())[is_phy_var_def,is_alloc_var_def,is_stack_var_def]>>
      disch_then(qspecl_then[`4`,`4*n`,`na`](SUBST1_TAC o SYM)) >>
      `(4*n) MOD 4 =0 ` by
        (`0<4:num` by DECIDE_TAC>>
        `∀k.(4:num)*k=k*4` by DECIDE_TAC>>
        metis_tac[arithmeticTheory.MOD_EQ_0])>>
      full_simp_tac(srw_ss())[])>>
    metis_tac[convention_partitions])
  >>
    fs[ssa_locals_rel_def,ssa_map_ok_def,domain_lookup]>>
    res_tac>>fs[set_vars_def,lookup_alist_insert]>>
    qpat_abbrev_tac`lss = ZIP(A,B)`>>
    `ALOOKUP lss v = NONE` by
      (fs[ALOOKUP_NONE,Abbr`lss`,MEM_MAP,FORALL_PROD,MEM_ZIP]>>
      rw[]>>
      Cases_on`n<LENGTH ls`>>fs[EL_MAP]>>
      qpat_assum`MAP A B = MAP C ls` (mp_tac o SYM o (Q.AP_TERM `EL n`))>>
      simp[EL_MAP,LENGTH_COUNT_LIST,EL_COUNT_LIST]>>rw[]>>
      res_tac>>fs[])>>
    fs[]>>
    ntac 3 (last_x_assum kall_tac)>>
    rfs[]);
val result = list_next_var_rename_move_preserve;
val _ = print "rms_full="; val _ = print_thm result; val _ = print "\n";
fun out label name = let val v = valOf(List.find (fn t => fst(dest_var t) = name) (fst(strip_forall(concl result)))) in print(label ^ "="); print_type(type_of v); print "\n" end;
val _ = out "rms_type_st" "st";
val _ = out "rms_type_cst" "cst";
val _ = out "rms_type_ssa" "ssa";
val _ = out "rms_type_na" "na";
val _ = out "rms_type_ls" "ls";
