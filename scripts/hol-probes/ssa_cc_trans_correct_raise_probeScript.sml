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
val exists_tac = qexists_tac`cst.permute` >>
 full_simp_tac(srw_ss())[evaluate_def,LET_THM,word_state_eq_rel_def,ssa_cc_trans_def];
val raise_case = prove(concl(Q.SPEC `Raise n` ssa_cc_trans_correct), rpt strip_tac >>
    exists_tac>>fs[]>>
    Cases_on`get_var n st`>>imp_res_tac ssa_locals_rel_get_var>>
    full_simp_tac(srw_ss())[get_vars_def,get_var_def,set_vars_def,lookup_alist_insert]>>
    full_simp_tac(srw_ss())[jump_exc_def]>>EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>> gvs[]);
fun out label th = (print(label ^ "="); print_thm th; print "\n");
val _ = out "raise_full" raise_case;
fun ty label name th = let val v=valOf(List.find(fn t => fst(dest_var t)=name)(free_vars(concl(SPEC_ALL th)))) in print(label ^ "="); print_type(type_of v); print "\n" end;
val _ = ty "raise_type_st" "st" raise_case;
val _ = ty "raise_type_cst" "cst" raise_case;
val _ = ty "raise_type_reg" "n" raise_case;
val _ = ty "raise_type_ssa" "ssa" raise_case;
val _ = ty "raise_type_na" "na" raise_case;
val _ = ty "raise_type_lt" "lt" raise_case;
