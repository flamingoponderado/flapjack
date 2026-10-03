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
val get_vars_case = prove (``
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
fun out label th = (print(label ^ "="); print_thm th; print "\n");
val _ = out "get_vars_full" get_vars_case;
fun ty label name th = let val v=valOf(List.find(fn t => fst(dest_var t)=name)(free_vars(concl(SPEC_ALL th)))) in print(label ^ "="); print_type(type_of v); print "\n" end;
val _ = ty "get_vars_type_source" "st" get_vars_case;
val _ = ty "get_vars_type_target" "cst" get_vars_case;
val _ = ty "get_vars_type_names" "ls" get_vars_case;
val _ = ty "get_vars_type_values" "y" get_vars_case;
val _ = ty "get_vars_type_ssa" "ssa" get_vars_case;
val _ = ty "get_vars_type_next" "na" get_vars_case;
