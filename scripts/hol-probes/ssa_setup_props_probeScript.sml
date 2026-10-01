load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory word_allocTheory wordSemTheory sptreeTheory reg_allocTheory;
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
val is_alloc_var_add = prove (``  is_alloc_var na ⇒ is_alloc_var (na+4)``,
  full_simp_tac(srw_ss())[is_alloc_var_def]>>
  (qspec_then `4` assume_tac arithmeticTheory.MOD_PLUS>>full_simp_tac(srw_ss())[]>>
    pop_assum (qspecl_then [`na`,`4`] assume_tac)>>
    rev_full_simp_tac(srw_ss())[]));
val is_stack_var_add = prove (``  is_stack_var na ⇒ is_stack_var (na+4)``,
  full_simp_tac(srw_ss())[is_stack_var_def]>>
  (qspec_then `4` assume_tac arithmeticTheory.MOD_PLUS>>full_simp_tac(srw_ss())[]>>
    pop_assum (qspecl_then [`na`,`4`] assume_tac)>>
    rev_full_simp_tac(srw_ss())[]));
val list_next_var_rename_props = prove (``  ∀ls ssa na ls' ssa' na'.
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
  metis_tac[is_alloc_var_add,is_stack_var_add]);
val get_vars_eq = prove (``  (set ls) SUBSET domain st.locals ==> ?z. get_vars ls st = SOME z /\
                                             z = MAP (\x. THE (lookup x st.locals)) ls``,
  Induct_on`ls`>>full_simp_tac(srw_ss())[get_vars_def,get_var_def]>>srw_tac[][]>>
  full_simp_tac(srw_ss())[domain_lookup]);
fun use_ALOOKUP_ALL_DISTINCT_MEM (g as (asl,w)) =
  let
    val tm = find_term(can(match_term(lhs(snd(dest_imp(concl
      ALOOKUP_ALL_DISTINCT_MEM)))))) w
    val (_,[al,k]) = strip_comb tm
  in
    mp_tac(ISPECL [al,k] (Q.GENL[`al`,`k`,`v`] ALOOKUP_ALL_DISTINCT_MEM))
  end g;
val is_phy_var_tac =
    full_simp_tac(srw_ss())[is_phy_var_def]>>
    `0<2:num` by DECIDE_TAC>>
    `∀k.(2:num)*k=k*2` by DECIDE_TAC>>
    metis_tac[arithmeticTheory.MOD_EQ_0];
val result = prove (``  is_alloc_var lim ∧
  domain st.locals = set (even_list n) ⇒
  let (mov:'a wordLang$prog,ssa,na) = setup_ssa n lim (prog:'a wordLang$prog) in
  let (res,cst) = evaluate(mov,st) in
    res = NONE ∧
    word_state_eq_rel st cst ∧
    ssa_map_ok na ssa ∧
    ssa_locals_rel na ssa st.locals cst.locals ∧
    is_alloc_var na ∧
    lim ≤ na``,
  srw_tac[][setup_ssa_def]>>
  full_simp_tac(srw_ss())[word_state_eq_rel_def,evaluate_def]>>
  imp_res_tac list_next_var_rename_lemma_1>>
  full_simp_tac(srw_ss())[LET_THM,MAP_ZIP,LENGTH_COUNT_LIST]>>
  full_simp_tac(srw_ss())[ALL_DISTINCT_MAP]>>
  `set args ⊆ domain st.locals` by full_simp_tac(srw_ss())[]>>
  imp_res_tac get_vars_eq>>
  full_simp_tac(srw_ss())[set_vars_def,state_component_equality]
  >>
    TRY(`ssa_map_ok lim LN` by
      full_simp_tac(srw_ss())[ssa_map_ok_def,lookup_def]>>
    imp_res_tac list_next_var_rename_props>>NO_TAC)>>
  full_simp_tac(srw_ss())[ssa_locals_rel_def]>>
  `ALL_DISTINCT args` by
    (unabbrev_all_tac>>
    full_simp_tac(srw_ss())[even_list_def,ALL_DISTINCT_GENLIST]>>srw_tac[][]>>
    DECIDE_TAC)>>
  imp_res_tac list_next_var_rename_lemma_2>>
  pop_assum kall_tac>>
  pop_assum(qspecl_then [`LN`,`lim`] mp_tac)>>
  LET_ELIM_TAC>>full_simp_tac(srw_ss())[]>>rev_full_simp_tac(srw_ss())[]
  >-
    (qpat_x_assum`A=cst.locals` (sym_sub_tac)>>
    full_simp_tac(srw_ss())[domain_alist_insert,LENGTH_COUNT_LIST]>>
    `x ∈ domain ssa` by full_simp_tac(srw_ss())[domain_lookup]>>
    qpat_x_assum `MAP f args = B` (sym_sub_tac)>>
    DISJ2_TAC>>
    full_simp_tac(srw_ss())[MEM_MAP]>>
    qexists_tac`x`>>
    `x ∈ domain ssa` by full_simp_tac(srw_ss())[domain_lookup]>>
    full_simp_tac(srw_ss())[]>>metis_tac[EXTENSION])
  >-
    (`x ∈ domain st.locals` by full_simp_tac(srw_ss())[domain_lookup]>>
    metis_tac[EXTENSION])
  >-
    (qpat_x_assum`A=cst.locals` (sym_sub_tac)>>
    full_simp_tac(srw_ss())[lookup_alist_insert,LENGTH_COUNT_LIST]>>
    full_simp_tac(srw_ss())[ALOOKUP_ALL_DISTINCT_EL]>>
    use_ALOOKUP_ALL_DISTINCT_MEM >>
    full_simp_tac(srw_ss())[MAP_ZIP,LENGTH_COUNT_LIST]>>
    strip_tac>>
    pop_assum(qspec_then `y` mp_tac)>>impl_tac
    >-
      (full_simp_tac(srw_ss())[MEM_ZIP,LENGTH_COUNT_LIST]>>
      `x ∈ set args` by metis_tac[domain_lookup]>>
      full_simp_tac(srw_ss())[MEM_EL]>>HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[EL_MAP]>>
      full_simp_tac(srw_ss())[LIST_EQ_REWRITE]>>last_x_assum(qspec_then`n''` assume_tac)>>
      rev_full_simp_tac(srw_ss())[]>>
      rev_full_simp_tac(srw_ss())[EL_MAP,LENGTH_COUNT_LIST])
    >>
    full_simp_tac(srw_ss())[])
  >>
    `x ∈ domain st.locals` by full_simp_tac(srw_ss())[domain_lookup]>>
    `MEM x args` by metis_tac[EXTENSION]>>
    full_simp_tac(srw_ss())[Abbr`args`]>>
    full_simp_tac(srw_ss())[even_list_def,MEM_GENLIST]>>
    `is_phy_var x` by is_phy_var_tac>>
    metis_tac[convention_partitions]);
val _ = print "setup_full="; val _ = print_thm result; val _ = print "\n";
fun out label name = let val vs = fst(strip_forall(concl result)) @ free_vars(concl result); val v = valOf(List.find (fn t => fst(dest_var t) = name) vs) in print(label ^ "="); print_type(type_of v); print "\n" end;
val _ = out "setup_type_lim" "lim";
val _ = out "setup_type_n" "n";
val _ = out "setup_type_st" "st";
val _ = out "setup_type_prog" "prog";
