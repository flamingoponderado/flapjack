load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory word_allocTheory wordSemTheory wordPropsTheory wordLangTheory sptreeTheory reg_allocTheory;
val _ = Globals.linewidth := 1000;
val body_statement = Q.SPEC `body` ssa_cc_trans_correct;
val outer_statement = Q.SPEC `MustTerminate body` ssa_cc_trans_correct;
val recursive_statement = mk_imp(concl body_statement, concl outer_statement);
val recursive_case = prove(recursive_statement,
  rpt strip_tac >>
  rw[ssa_cc_trans_def] >> rpt(pairarg_tac >> gvs[]) >>
  fs[evaluate_def,word_state_eq_rel_def] >>
  first_x_assum(qspecl_then[
    `st with <|clock:=MustTerminate_limit (:'a);termdep:=st.termdep-1|>`,
    `cst with <|clock:=MustTerminate_limit (:'a);termdep:=st.termdep-1|>`,
    `ssa`,`na`,`lt`] mp_tac) >>
  impl_tac >- fs[every_var_def] >> strip_tac >>
  qexists_tac`perm'` >> simp[] >> IF_CASES_TAC >> fs[] >>
  rpt(pairarg_tac >> gvs[]) >> gvs[AllCaseEqs()]);
fun out label th = (print(label ^ "="); print_thm th; print "\n");
val _ = out "sm_recursive_full" recursive_case;
val _ = out "sm_original_full" outer_statement;
fun ty label name th = let val v=valOf(List.find(fn t => fst(dest_var t)=name)(free_vars(concl(SPEC_ALL th)))) in print(label ^ "="); print_type(type_of v); print "\n" end;
val _ = ty "sm_type_st" "st" outer_statement;
val _ = ty "sm_type_cst" "cst" outer_statement;
val _ = ty "sm_type_body" "body" outer_statement;
val _ = ty "sm_type_ssa" "ssa" outer_statement;
val _ = ty "sm_type_na" "na" outer_statement;
val _ = ty "sm_type_lt" "lt" outer_statement;
