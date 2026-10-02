load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory word_allocTheory wordSemTheory wordPropsTheory wordLangTheory sptreeTheory reg_allocTheory;
val _ = Globals.linewidth := 1000;
val ssa_locals_rel_set_var = prove (``
  ssa_locals_rel na ssa stl cstl ∧
  ssa_map_ok na ssa ∧
  n < na ⇒
  ssa_locals_rel (na+4) (insert n na ssa) (insert n w stl) (insert na w cstl)``,
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
val exists_tac = qexists_tac`cst.permute` >>
 full_simp_tac(srw_ss())[evaluate_def,LET_THM,word_state_eq_rel_def,ssa_cc_trans_def];
val const_case = prove(concl(Q.SPEC `Inst (Const n c)` ssa_cc_trans_correct),
 rpt strip_tac >> exists_tac >>
 fs[next_var_rename_def,ssa_cc_trans_inst_def,inst_def,assign_def,evaluate_def,LET_THM] >>
 Cases_on`word_exp st (Const c)` >>
 full_simp_tac(srw_ss())[set_var_def,word_exp_def] >>
 match_mp_tac ssa_locals_rel_set_var >>
 full_simp_tac(srw_ss())[every_var_inst_def,every_var_def]);
fun out label th = (print(label ^ "="); print_thm th; print "\n");
val _ = out "inst_const_full" const_case;
fun ty label name th = let val v=valOf(List.find(fn t => fst(dest_var t)=name)(free_vars(concl(SPEC_ALL th)))) in print(label ^ "="); print_type(type_of v); print "\n" end;
val _ = ty "inst_const_type_st" "st" const_case;
val _ = ty "inst_const_type_cst" "cst" const_case;
val _ = ty "inst_const_type_reg" "n" const_case;
val _ = ty "inst_const_type_word" "c" const_case;
val _ = ty "inst_const_type_ssa" "ssa" const_case;
val _ = ty "inst_const_type_next" "na" const_case;
val _ = ty "inst_const_type_tables" "lt" const_case;
