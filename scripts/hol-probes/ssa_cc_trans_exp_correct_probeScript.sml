load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory word_allocTheory wordSemTheory wordPropsTheory wordLangTheory sptreeTheory reg_allocTheory;
val _ = Globals.linewidth := 1000;
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
val result = ssa_cc_trans_exp_correct;
val _ = print "sec_full="; val _ = print_thm result; val _ = print "\n";
val variables = fst (strip_forall (concl result));
fun out label name = let val variable = valOf (List.find (fn v => fst (dest_var v) = name) variables) in print (label ^ "="); print_type (type_of variable); print "\n" end;
val _ = out "sec_type_st" "st";
val _ = out "sec_type_w" "w";
val _ = out "sec_type_cst" "cst";
val _ = out "sec_type_ssa" "ssa";
val _ = out "sec_type_na" "na";
val _ = out "sec_type_res" "res";
