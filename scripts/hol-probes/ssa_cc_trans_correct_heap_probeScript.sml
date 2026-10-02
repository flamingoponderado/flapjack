load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory word_allocTheory wordSemTheory wordPropsTheory wordLangTheory sptreeTheory reg_allocTheory;
val _ = Globals.linewidth := 1000;
val ssa_locals_rel_get_var = prove (``ssa_locals_rel na ssa st.locals cst.locals ∧
  get_var n st = SOME x
  ⇒
  get_var (option_lookup ssa n) cst = SOME x``,
  full_simp_tac(srw_ss())[get_var_def,ssa_locals_rel_def,strong_locals_rel_def,option_lookup_def]>>
  srw_tac[][]>>
  FULL_CASE_TAC>>full_simp_tac(srw_ss())[domain_lookup]>>
  first_x_assum(qspecl_then[`n`,`x`] assume_tac)>>rev_full_simp_tac(srw_ss())[]);
val setVarStatement = ``ssa_locals_rel na ssa stl cstl ∧
  ssa_map_ok na ssa ∧
  n < na ⇒
  ssa_locals_rel (na+4) (insert n na ssa) (insert n w stl) (insert na w cstl)``;
val ssa_locals_rel_set_var = prove(setVarStatement,
srw_tac[][ssa_locals_rel_def]>>
  full_simp_tac(srw_ss())[lookup_insert]>>Cases_on`x=n`>>full_simp_tac(srw_ss())[]
  >-
    metis_tac[]
  >-
    (res_tac>>
    full_simp_tac(srw_ss())[domain_lookup,ssa_map_ok_def]>>
    first_x_assum(qspecl_then[`x`,`v`]assume_tac)>>
    (*Next part is a key reasoning step --
      We only have alloc_vars < na in the range of ssa
      Otherwise, the new one may overwrite an old mapping
    *)
    rev_full_simp_tac(srw_ss())[]>>
    `v ≠ na` by DECIDE_TAC >>
    full_simp_tac(srw_ss())[])
  >-
    DECIDE_TAC
  >>
    (*Finally, this illustrates need for <na assumption on st.locals*)
    full_simp_tac(srw_ss())[ssa_map_ok_def]>>res_tac>>full_simp_tac(srw_ss())[]>>DECIDE_TAC);
val ssa_cc_trans_exp_correct = prove (``  ∀st w cst ssa na res.
  word_exp st w = SOME res ∧
  word_state_eq_rel st cst ∧
  ssa_locals_rel na ssa st.locals cst.locals
  ⇒
  word_exp cst (ssa_cc_trans_exp ssa w) = SOME res``,
  ho_match_mp_tac word_exp_ind>>srw_tac[][]>>
  full_simp_tac(srw_ss())[word_exp_def,ssa_cc_trans_exp_def]>>
  qpat_x_assum`A=SOME res` mp_tac
  >-
    (fs[get_var_def,ssa_locals_rel_def,word_state_eq_rel_def]>>rw[]>>
    res_tac>>rpt(qpat_x_assum`!x.P` kall_tac)>>
    fs[domain_lookup,option_lookup_def]>>
    rfs[])
  >-
    full_simp_tac(srw_ss())[word_state_eq_rel_def,get_store_def]
  >-
    (Cases_on`word_exp st w`>>
    res_tac>>full_simp_tac(srw_ss())[word_state_eq_rel_def,mem_load_def])
  >-
    (qpat_abbrev_tac`ls = MAP A B`>>
    qpat_abbrev_tac`ls' = MAP A B`>>
    TOP_CASE_TAC>>simp[]>>
    `ls = ls'` by
      (imp_res_tac the_words_EVERY_IS_SOME>>
      unabbrev_all_tac>>fs[MAP_EQ_f,MAP_MAP_o]>>
      fs[EVERY_MAP,EVERY_MEM]>>
      rw[]>>res_tac>>
      fs[IS_SOME_EXISTS])>>
    fs[])
  >-
    (strip_tac>>
    gvs[AllCaseEqs()]>>
    res_tac>>gvs[]));
val exists_tac = qexists_tac`cst.permute` >>
 full_simp_tac(srw_ss())[evaluate_def,LET_THM,word_state_eq_rel_def,ssa_cc_trans_def];
val heap_case = prove(concl(Q.SPEC `OpCurrHeap b n m` ssa_cc_trans_correct), rpt strip_tac >>
    exists_tac>>
    EVERY_CASE_TAC>>full_simp_tac(srw_ss())[next_var_rename_def]>>
    imp_res_tac ssa_locals_rel_get_var>>
    imp_res_tac ssa_cc_trans_exp_correct>>full_simp_tac(srw_ss())[word_state_eq_rel_def]>>
    rev_full_simp_tac(srw_ss())[evaluate_def]>>
    fs[set_var_def,set_store_def,ssa_cc_trans_exp_def]>>
    match_mp_tac ssa_locals_rel_set_var>>
    full_simp_tac(srw_ss())[every_var_def]);
fun out label th = (print(label ^ "="); print_thm th; print "\n");
val _ = out "heap_full" heap_case;
fun ty label name th = let val v=valOf(List.find(fn t => fst(dest_var t)=name)(free_vars(concl(SPEC_ALL th)))) in print(label ^ "="); print_type(type_of v); print "\n" end;
val _ = ty "heap_type_st" "st" heap_case;
val _ = ty "heap_type_cst" "cst" heap_case;
val _ = ty "heap_type_operator" "b" heap_case;
val _ = ty "heap_type_dst" "n" heap_case;
val _ = ty "heap_type_src" "m" heap_case;
val _ = ty "heap_type_lt" "lt" heap_case;
