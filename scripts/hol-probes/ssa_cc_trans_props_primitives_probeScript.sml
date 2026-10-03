load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory word_allocTheory wordSemTheory wordPropsTheory wordLangTheory sptreeTheory reg_allocTheory;
val _ = Globals.linewidth := 1000;
val ssa_map_ok_extend = GEN_ALL (prove (``  ssa_map_ok na ssa ∧
  ¬is_phy_var na ⇒
  ssa_map_ok (na+4) (insert h na ssa)``,
  full_simp_tac(srw_ss())[ssa_map_ok_def]>>
  srw_tac[][]>>full_simp_tac(srw_ss())[lookup_insert]>>
  Cases_on`x=h`>>full_simp_tac(srw_ss())[]>>
  res_tac>-
    DECIDE_TAC));
val is_alloc_var_add = GEN_ALL (prove (``  is_alloc_var na ⇒ is_alloc_var (na+4)``,
  full_simp_tac(srw_ss())[is_alloc_var_def]>>
  (qspec_then `4` assume_tac arithmeticTheory.MOD_PLUS>>full_simp_tac(srw_ss())[]>>
    pop_assum (qspecl_then [`na`,`4`] assume_tac)>>
    rev_full_simp_tac(srw_ss())[])));
val ssa_cc_trans_inst_props = GEN_ALL (prove (``  ∀i ssa na i' ssa' na'.
  ssa_cc_trans_inst i ssa na = (i',ssa',na') ==>
  ssa_map_ok na ssa ∧
  is_alloc_var na
  ⇒
  na ≤ na' ∧
  is_alloc_var na' ∧
  ssa_map_ok na' ssa'``,
  ho_match_mp_tac ssa_cc_trans_inst_ind>>rw[]>>
  gvs[ssa_cc_trans_inst_def,next_var_rename_def,AllCaseEqs()]>>
  rpt(pairarg_tac>>gvs[])>>
  `na + 8 = na + 4 +4` by fs[]>>
  metis_tac[is_alloc_var_add,ssa_map_ok_extend,convention_partitions]));
val ssa_cc_trans_inst_props = prove (``∀i ssa na i' ssa' na'.
  ssa_cc_trans_inst i ssa na = (i',ssa',na') ==>
  ssa_map_ok na ssa ∧
  is_alloc_var na
  ⇒
  na ≤ na' ∧
  is_alloc_var na' ∧
  ssa_map_ok na' ssa'``, ho_match_mp_tac ssa_cc_trans_inst_ind>>rw[]>>
  gvs[ssa_cc_trans_inst_def,next_var_rename_def,AllCaseEqs()]>>
  rpt(pairarg_tac>>gvs[])>>
  `na + 8 = na + 4 +4` by fs[]>>
  metis_tac[is_alloc_var_add,ssa_map_ok_extend,convention_partitions]);
val exp_tac = (LET_ELIM_TAC>>full_simp_tac(srw_ss())[next_var_rename_def]>>
    TRY(DECIDE_TAC)>>
    metis_tac[ssa_map_ok_extend,convention_partitions,is_alloc_var_add]);
val property = ``λprog ssa na lt. ∀progOut ssaOut naOut. ssa_cc_trans prog ssa na lt = (progOut,ssaOut,naOut) ⇒ ssa_map_ok na ssa ∧ is_alloc_var na ⇒ na ≤ naOut ∧ is_alloc_var naOut ∧ ssa_map_ok naOut ssaOut``;
val clauses = strip_conj(fst(dest_imp(concl(BETA_RULE(ISPEC property ssa_cc_trans_ind)))));
val case_0 = prove(List.nth(clauses,0), rpt gen_tac >> full_simp_tac(srw_ss())[ssa_cc_trans_def] >> (rw[]));
val case_2 = prove(List.nth(clauses,2), rpt gen_tac >> full_simp_tac(srw_ss())[ssa_cc_trans_def] >> (LET_ELIM_TAC>>fs[next_var_rename_def]
    >- (
      rw[]>>
      `is_alloc_var ((d2+4)+4)` by
        fs[is_alloc_var_add]>>
      fs[])>>
    drule ssa_map_ok_extend >>
    disch_then(qspec_then `d` mp_tac)>>
    impl_tac >-
      metis_tac[convention_partitions]>>
    rw[]>>
    drule ssa_map_ok_extend >>
    disch_then(qspec_then `c` mp_tac)>>
    impl_tac >- metis_tac[convention_partitions,is_alloc_var_add]>>
    simp[]));
val case_3 = prove(List.nth(clauses,3), rpt gen_tac >> full_simp_tac(srw_ss())[ssa_cc_trans_def] >> (LET_ELIM_TAC>>full_simp_tac(srw_ss())[]>>metis_tac[ssa_cc_trans_inst_props]));
val case_4 = prove(List.nth(clauses,4), rpt gen_tac >> full_simp_tac(srw_ss())[ssa_cc_trans_def] >> (exp_tac));
val case_5 = prove(List.nth(clauses,5), rpt gen_tac >> full_simp_tac(srw_ss())[ssa_cc_trans_def] >> (exp_tac));
val case_6 = prove(List.nth(clauses,6), rpt gen_tac >> full_simp_tac(srw_ss())[ssa_cc_trans_def] >> (exp_tac));
val case_11 = prove(List.nth(clauses,11), rpt gen_tac >> full_simp_tac(srw_ss())[ssa_cc_trans_def] >> (exp_tac));
val case_12 = prove(List.nth(clauses,12), rpt gen_tac >> full_simp_tac(srw_ss())[ssa_cc_trans_def] >> (exp_tac));
val case_13 = prove(List.nth(clauses,13), rpt gen_tac >> full_simp_tac(srw_ss())[ssa_cc_trans_def] >> (exp_tac));
val case_14 = prove(List.nth(clauses,14), rpt gen_tac >> full_simp_tac(srw_ss())[ssa_cc_trans_def] >> (exp_tac));
val case_15 = prove(List.nth(clauses,15), rpt gen_tac >> full_simp_tac(srw_ss())[ssa_cc_trans_def] >> (exp_tac));
val case_16 = prove(List.nth(clauses,16), rpt gen_tac >> full_simp_tac(srw_ss())[ssa_cc_trans_def] >> (exp_tac));
val case_18 = prove(List.nth(clauses,18), rpt gen_tac >> full_simp_tac(srw_ss())[ssa_cc_trans_def] >> (rw[]>>fs[]));
val case_19 = prove(List.nth(clauses,19), rpt gen_tac >> full_simp_tac(srw_ss())[ssa_cc_trans_def] >> (rw[]>>fs[]));
val case_23 = prove(List.nth(clauses,23), rpt gen_tac >> full_simp_tac(srw_ss())[ssa_cc_trans_def] >> (rpt gen_tac >>
    simp[LET_THM] >>
    IF_CASES_TAC
    >- (rw[] >> simp[]) >>
    pairarg_tac >>
    simp[] >>
    rpt $ disch_then strip_assume_tac >>
    gvs[next_var_rename_def] >>
    conj_tac >- fs[is_alloc_var_def] >>
    drule_then irule ssa_map_ok_extend >>
    metis_tac[convention_partitions] ));
fun out label th = (print(label ^ "="); print_thm th; print "\n");
val _ = out "spp_case_0" case_0;
val _ = out "spp_case_2" case_2;
val _ = out "spp_case_3" case_3;
val _ = out "spp_case_4" case_4;
val _ = out "spp_case_5" case_5;
val _ = out "spp_case_6" case_6;
val _ = out "spp_case_11" case_11;
val _ = out "spp_case_12" case_12;
val _ = out "spp_case_13" case_13;
val _ = out "spp_case_14" case_14;
val _ = out "spp_case_15" case_15;
val _ = out "spp_case_16" case_16;
val _ = out "spp_case_18" case_18;
val _ = out "spp_case_19" case_19;
val _ = out "spp_case_23" case_23;
fun ty label name th = let val vs = fst(strip_forall(concl th)) @ free_vars(concl th); val v = valOf(List.find (fn t => fst(dest_var t) = name) vs) in print(label ^ "="); print_type(type_of v); print "\n" end;
val _ = ty "spp_0_type_ssa" "ssa" case_0;
val _ = ty "spp_0_type_na" "na" case_0;
val _ = ty "spp_0_type_lt" "lt" case_0;
val _ = ty "spp_0_type_progOut" "progOut" case_0;
val _ = ty "spp_0_type_ssaOut" "ssaOut" case_0;
val _ = ty "spp_0_type_naOut" "naOut" case_0;
val _ = ty "spp_2_type_a" "a" case_2;
val _ = ty "spp_2_type_b" "b" case_2;
val _ = ty "spp_2_type_c" "c" case_2;
val _ = ty "spp_2_type_d" "d" case_2;
val _ = ty "spp_2_type_ws" "ws" case_2;
val _ = ty "spp_3_type_i" "i" case_3;
val _ = ty "spp_4_type_num" "num" case_4;
val _ = ty "spp_4_type_exp" "exp" case_4;
val _ = ty "spp_5_type_num" "num" case_5;
val _ = ty "spp_5_type_store" "store" case_5;
val _ = ty "spp_6_type_exp" "exp" case_6;
val _ = ty "spp_6_type_num" "num" case_6;
val _ = ty "spp_11_type_num" "num" case_11;
val _ = ty "spp_12_type_b" "b" case_12;
val _ = ty "spp_12_type_dst" "dst" case_12;
val _ = ty "spp_12_type_src" "src" case_12;
val _ = ty "spp_13_type_num" "num" case_13;
val _ = ty "spp_13_type_nums" "nums" case_13;
val _ = ty "spp_15_type_n" "n" case_15;
val _ = ty "spp_15_type_exp" "exp" case_15;
val _ = ty "spp_16_type_r" "r" case_16;
val _ = ty "spp_16_type_l1" "l1" case_16;
val _ = ty "spp_18_type_r1" "r1" case_18;
val _ = ty "spp_18_type_r2" "r2" case_18;
val _ = ty "spp_19_type_r1" "r1" case_19;
val _ = ty "spp_19_type_r2" "r2" case_19;
val _ = ty "spp_23_type_op" "op" case_23;
val _ = ty "spp_23_type_v" "v" case_23;
val _ = ty "spp_23_type_exp" "exp" case_23;
