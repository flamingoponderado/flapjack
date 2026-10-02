load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory word_allocTheory wordSemTheory wordPropsTheory wordLangTheory sptreeTheory reg_allocTheory;
val _ = Globals.linewidth := 1000;
open wordConvsTheory;
val ssa_locals_rel_more = prove (``ssa_locals_rel na ssa stlocs cstlocs ∧ na ≤ na' ⇒
  ssa_locals_rel na' ssa stlocs cstlocs``,
  srw_tac[][ssa_locals_rel_def] >> full_simp_tac(srw_ss())[] >- metis_tac[] >>
  res_tac >> full_simp_tac(srw_ss())[] >> DECIDE_TAC);
val first_statement = Q.SPEC `p` ssa_cc_trans_correct;
val second_statement = Q.SPEC `p0` ssa_cc_trans_correct;
val outer_statement = Q.SPEC `Seq p p0` ssa_cc_trans_correct;
val recursive_statement = mk_imp(concl first_statement, mk_imp(concl second_statement, concl outer_statement));
val recursive_case = prove(recursive_statement, rpt strip_tac >>
    srw_tac[][]>>full_simp_tac(srw_ss())[evaluate_def,ssa_cc_trans_def,LET_THM]>>
    qpat_x_assum `∀st cst ssa na lt. word_state_eq_rel st cst ∧ _ ∧ is_alloc_var na ∧ every_var _ p ∧ _ ⇒ _` (qspecl_then[`st`,`cst`,`ssa`,`na`,`lt`] mp_tac)>>
    impl_tac>>full_simp_tac(srw_ss())[every_var_def]>>srw_tac[][]>>
    Cases_on`ssa_cc_trans p ssa na lt`>>Cases_on`r`>>full_simp_tac(srw_ss())[]>>
    Cases_on`ssa_cc_trans p0 q' r' lt`>>Cases_on`r`>>full_simp_tac(srw_ss())[]>>
    full_simp_tac(srw_ss())[evaluate_def,LET_THM]>>
    Cases_on`evaluate(p,st with permute:=perm')`>>full_simp_tac(srw_ss())[]
    >- (qexists_tac`perm'`>>full_simp_tac(srw_ss())[]) >>
    Cases_on`evaluate(q,cst)`>>full_simp_tac(srw_ss())[]>>
    reverse (Cases_on`q'''''`)
    >-
      (qexists_tac`perm'`>>srw_tac[][]>>full_simp_tac(srw_ss())[]>>
       Cases_on`x`>>fs[]>>
       every_case_tac>>fs[]>>
       imp_res_tac ssa_cc_trans_props>>
       metis_tac[ssa_locals_rel_more])
    >>
    full_simp_tac(srw_ss())[]>>
    qpat_x_assum `∀st cst ssa na lt. word_state_eq_rel st cst ∧ _ ∧ is_alloc_var na ∧ every_var _ p0 ∧ _ ⇒ _` (qspecl_then[`r`,`r'''`,`q'`,`r'`,`lt`] mp_tac)>>
    impl_tac>-
      (rev_full_simp_tac(srw_ss())[]>>imp_res_tac ssa_cc_trans_props>>
      full_simp_tac(srw_ss())[]>>
      match_mp_tac every_var_mono>>
      HINT_EXISTS_TAC>>
      full_simp_tac(srw_ss())[]>>DECIDE_TAC)>>
    srw_tac[][]>>
    qspecl_then[`p`,`st with permute:=perm'`,`perm''`]
      assume_tac permute_swap_lemma>>
    rev_full_simp_tac(srw_ss())[LET_THM]>>
    qexists_tac`perm'''`>>srw_tac[][]>>full_simp_tac(srw_ss())[]);
fun out label th = (print(label ^ "="); print_thm th; print "\n");
val _ = out "sq_recursive_full" recursive_case;
val _ = out "sq_original_full" outer_statement;
fun ty label name th = let val v=valOf(List.find(fn t => fst(dest_var t)=name)(free_vars(concl(SPEC_ALL th)))) in print(label ^ "="); print_type(type_of v); print "\n" end;
val _ = ty "sq_type_st" "st" outer_statement;
val _ = ty "sq_type_cst" "cst" outer_statement;
val _ = ty "sq_type_first" "p" outer_statement;
val _ = ty "sq_type_second" "p0" outer_statement;
val _ = ty "sq_type_ssa" "ssa" outer_statement;
val _ = ty "sq_type_na" "na" outer_statement;
val _ = ty "sq_type_lt" "lt" outer_statement;
