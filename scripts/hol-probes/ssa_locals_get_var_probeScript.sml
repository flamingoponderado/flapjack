load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory word_allocTheory wordSemTheory wordPropsTheory wordLangTheory sptreeTheory reg_allocTheory;
val _ = Globals.linewidth := 1000;
val locals_get_var = prove (``ssa_locals_rel na ssa st.locals cst.locals ∧
  get_var n st = SOME x
  ⇒
  get_var (option_lookup ssa n) cst = SOME x``,
  full_simp_tac(srw_ss())[get_var_def,ssa_locals_rel_def,strong_locals_rel_def,option_lookup_def]>>
  srw_tac[][]>>
  FULL_CASE_TAC>>full_simp_tac(srw_ss())[domain_lookup]>>
  first_x_assum(qspecl_then[`n`,`x`] assume_tac)>>rev_full_simp_tac(srw_ss())[]);
val _ = (print "lg_full="; print_thm locals_get_var; print "\n");
fun ty label name = let val v=valOf(List.find(fn t => fst(dest_var t)=name)(free_vars(concl locals_get_var))) in print(label ^ "="); print_type(type_of v); print "\n" end;
val _ = ty "lg_type_st" "st";
val _ = ty "lg_type_cst" "cst";
val _ = ty "lg_type_ssa" "ssa";
val _ = ty "lg_type_na" "na";
val _ = ty "lg_type_n" "n";
val _ = ty "lg_type_x" "x";
