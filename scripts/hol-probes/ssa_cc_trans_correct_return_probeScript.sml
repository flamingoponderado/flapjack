load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory word_allocTheory wordSemTheory wordPropsTheory wordLangTheory sptreeTheory reg_allocTheory;
val _ = Globals.linewidth := 1000;
val ssa_locals_rel_get_var = prove (``
  ssa_locals_rel na ssa st.locals cst.locals ∧
  get_var n st = SOME x
  ⇒
  get_var (option_lookup ssa n) cst = SOME x``,
  full_simp_tac(srw_ss())[get_var_def,ssa_locals_rel_def,strong_locals_rel_def,option_lookup_def]>>
  srw_tac[][]>>
  FULL_CASE_TAC>>full_simp_tac(srw_ss())[domain_lookup]>>
  first_x_assum(qspecl_then[`n`,`x`] assume_tac)>>rev_full_simp_tac(srw_ss())[]);
val ssa_locals_rel_get_vars = prove (``
  ∀ls y na ssa st cst.
  ssa_locals_rel na ssa st.locals cst.locals ∧
  get_vars ls st = SOME y
  ⇒
  get_vars (MAP (option_lookup ssa) ls) cst = SOME y``,
  Induct>>full_simp_tac(srw_ss())[get_vars_def]>>srw_tac[][]>>
  Cases_on`get_var h st`>>full_simp_tac(srw_ss())[]>>
  imp_res_tac ssa_locals_rel_get_var>>full_simp_tac(srw_ss())[]>>
  Cases_on`get_vars ls st`>>full_simp_tac(srw_ss())[]>>
  res_tac>>full_simp_tac(srw_ss())[]);
val get_vars_list_insert_eq_gen = prove (``
  !ls x locs a b. (LENGTH ls = LENGTH x /\ ALL_DISTINCT ls /\
                  LENGTH a = LENGTH b /\ !e. MEM e ls ==> ~MEM e a)
  ==> get_vars ls (st with locals := alist_insert (a++ls) (b++x) locs) = SOME x``,
  ho_match_mp_tac alist_insert_ind>>
  srw_tac[][]>- (full_simp_tac(srw_ss())[get_vars_def])>>
  full_simp_tac(srw_ss())[get_vars_def,get_var_def,lookup_alist_insert]>>
  `LENGTH (ls::ls') = LENGTH (x::x')` by full_simp_tac(srw_ss())[]>>
  IMP_RES_TAC rich_listTheory.ZIP_APPEND>>
  ntac 9 (pop_assum (SUBST1_TAC o SYM))>>
  full_simp_tac(srw_ss())[ALOOKUP_APPEND]>>
  first_assum(qspec_then `ls` assume_tac)>>full_simp_tac(srw_ss())[]>>
  `ALOOKUP (ZIP (a,b)) ls = NONE` by metis_tac[ALOOKUP_NONE,MEM_MAP,MAP_ZIP]>>
  full_simp_tac(srw_ss())[]>>
  first_x_assum(qspecl_then [`a++[ls]`,`b++[x]`] assume_tac)>>
  `LENGTH (a++[ls]) = LENGTH (b++[x])` by full_simp_tac(srw_ss())[]>> rev_full_simp_tac(srw_ss())[]>>
  `a++[ls]++ls' = a++ls::ls' /\ b++[x]++x' = b++x::x'` by full_simp_tac(srw_ss())[]>>
  ntac 2 (pop_assum SUBST_ALL_TAC)>> full_simp_tac(srw_ss())[]);
val get_vars_set_vars_eq = prove (``
  ∀ls x.
  ALL_DISTINCT ls ∧ LENGTH x = LENGTH ls ⇒
  get_vars ls (set_vars ls x cst) = SOME x``,
  full_simp_tac(srw_ss())[get_vars_def,set_vars_def]>>srw_tac[][]>>
  Q.ISPECL_THEN [`cst`,`ls`,`x`,`cst.locals`,`[]:num list`
    ,`[]:'a word_loc list`] mp_tac (GEN_ALL get_vars_list_insert_eq_gen)>>
  impl_tac>>full_simp_tac(srw_ss())[]);
val ssa_locals_rel_ignore_list_insert = prove (``
  ssa_map_ok na ssa ∧
  ssa_locals_rel na ssa st.locals cst.locals ∧
  EVERY is_phy_var ls ∧
  LENGTH ls = LENGTH x
  ⇒
  ssa_locals_rel na ssa st.locals (alist_insert ls x cst.locals)``,
  srw_tac[][ssa_locals_rel_def,ssa_map_ok_def]>>
  full_simp_tac(srw_ss())[domain_alist_insert,lookup_alist_insert]>-
    metis_tac[]
  >>
  res_tac>>
  full_simp_tac(srw_ss())[domain_lookup]>>
  res_tac>>
  `ALOOKUP (ZIP(ls,x)) v = NONE` by
    (srw_tac[][ALOOKUP_FAILS,MEM_ZIP]>>
    metis_tac[EVERY_EL])>>
  full_simp_tac(srw_ss())[]);
val exists_tac = qexists_tac`cst.permute` >>
 full_simp_tac(srw_ss())[evaluate_def,LET_THM,word_state_eq_rel_def,ssa_cc_trans_def];
val return_case = prove(concl(Q.SPEC `Return n l` ssa_cc_trans_correct), rpt strip_tac >>
    exists_tac>>fs[]>>
    Cases_on`get_var n st`>> fs[] >>
    Cases_on `x` >> fs[] >>
    Cases_on`get_vars l st`>> fs[] >>
    full_simp_tac(srw_ss())[MAP_ZIP,ALL_DISTINCT_GENLIST] >>
    imp_res_tac ssa_locals_rel_get_vars>>
    full_simp_tac(srw_ss())[]>>
    imp_res_tac ssa_locals_rel_get_var>>
    full_simp_tac(srw_ss())[]>>
    full_simp_tac(srw_ss())[set_vars_def]>>
    imp_res_tac ssa_locals_rel_ignore_list_insert>>
    ntac 4 (pop_assum kall_tac)>>
    pop_assum(qspecl_then [`x`,`(GENLIST (λx. 2 * (x + 1)) (LENGTH l))`] mp_tac)>>
    pop_assum kall_tac >>
    impl_tac>- (full_simp_tac(srw_ss())[LENGTH_GENLIST]>>
   imp_res_tac get_vars_length_lemma >> gvs[]) >>
    impl_tac>- full_simp_tac(srw_ss())[EVERY_GENLIST,is_phy_var_def] >>
    srw_tac[][]>>full_simp_tac(srw_ss())[alist_insert_def]>>
    qpat_abbrev_tac`rcst=cst with locals:=A`>>
    rename1 `get_var _ cst = SOME (Loc l1 l2)`>>
    Q.ISPECL_THEN [`Loc l1 l2`,`st`,`ssa`,`na`,`n`,`rcst`] assume_tac (GEN_ALL ssa_locals_rel_get_var)>>
    pop_assum mp_tac >>
    impl_tac >- (unabbrev_all_tac>>rfs[])>>
    strip_tac >> full_simp_tac(srw_ss())[] >>
    unabbrev_all_tac >> full_simp_tac (srw_ss())[GSYM set_vars_def] >>
    DEP_REWRITE_TAC[get_vars_set_vars_eq] >>
    fs[ALL_DISTINCT_GENLIST,LENGTH_GENLIST] >>
    CONJ_TAC >-
    (imp_res_tac get_vars_length_lemma >> gvs[]) >>
    fs[flush_state_def]);
fun out label th = (print(label ^ "="); print_thm th; print "\n");
val _ = out "return_full" return_case;
fun ty label name th = let val v=valOf(List.find(fn t => fst(dest_var t)=name)(free_vars(concl(SPEC_ALL th)))) in print(label ^ "="); print_type(type_of v); print "\n" end;
val _ = ty "return_type_st" "st" return_case;
val _ = ty "return_type_cst" "cst" return_case;
val _ = ty "return_type_label_reg" "n" return_case;
val _ = ty "return_type_value_regs" "l" return_case;
val _ = ty "return_type_ssa" "ssa" return_case;
val _ = ty "return_type_next" "na" return_case;
val _ = ty "return_type_tables" "lt" return_case;
