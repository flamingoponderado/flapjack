load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory word_allocTheory wordSemTheory wordPropsTheory wordLangTheory sptreeTheory reg_allocTheory;
val _ = Globals.linewidth := 1000;
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
val ssa_cc_trans_props_Move = prove (``∀pri ls ssa na lt progOut ssaOut naOut.
 ssa_cc_trans (Move pri ls) ssa na lt = (progOut,ssaOut,naOut) ⇒
 ssa_map_ok na ssa ∧ is_alloc_var na ⇒
 na ≤ naOut ∧ is_alloc_var naOut ∧ ssa_map_ok naOut ssaOut``,
 rpt gen_tac >> full_simp_tac(srw_ss())[ssa_cc_trans_def] >>
 LET_ELIM_TAC>>
    full_simp_tac(srw_ss())[]
    >-
      metis_tac[list_next_var_rename_props]
    >-
      metis_tac[list_next_var_rename_props]
    >- (
      drule_at Any list_next_var_rename_props>>
      simp[]>>
      disch_then drule>>rw[]>>
      drule ssa_map_ok_force_rename>>
      disch_then match_mp_tac>>
      DEP_REWRITE_TAC[every_zip_snd]>>
      drule list_next_var_rename_lemma_1>>
      unabbrev_all_tac>>rw[EVERY_MEM,MEM_FILTER]>>
      pairarg_tac>>
      gvs[LENGTH_COUNT_LIST,MEM_MAP,MEM_COUNT_LIST,MEM_ZIP,EL_MAP,EL_COUNT_LIST]>>
      rename1`4 * xx + na`>>
      `is_alloc_var (4 * xx + na)` by
        gvs[is_alloc_var_def]>>
      metis_tac[convention_partitions]) );
val result = ssa_cc_trans_props_Move;
val _ = print "spm_full="; val _ = print_thm result; val _ = print "\n";
fun out label name = let val vars = fst(strip_forall(concl result)) @ free_vars(concl result); val v = valOf(List.find (fn t => fst(dest_var t) = name) vars) in print(label ^ "="); print_type(type_of v); print "\n" end;
val _ = out "spm_type_pri" "pri";
val _ = out "spm_type_ls" "ls";
val _ = out "spm_type_ssa" "ssa";
val _ = out "spm_type_na" "na";
val _ = out "spm_type_lt" "lt";
val _ = out "spm_type_progOut" "progOut";
val _ = out "spm_type_ssaOut" "ssaOut";
val _ = out "spm_type_naOut" "naOut";
