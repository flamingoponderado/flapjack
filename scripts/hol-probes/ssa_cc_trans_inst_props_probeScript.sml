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
val result = ssa_cc_trans_inst_props;
val _ = print "sip_full="; val _ = print_thm result; val _ = print "\n";
fun out label name = let val vars = fst(strip_forall(concl result)) @ free_vars(concl result); val v = valOf(List.find (fn t => fst(dest_var t) = name) vars) in print(label ^ "="); print_type(type_of v); print "\n" end;
val _ = out "sip_type_i" "i";
val _ = out "sip_type_ssa" "ssa";
val _ = out "sip_type_na" "na";
val _ = out "sip_type_iOut" "i'";
val _ = out "sip_type_ssaOut" "ssa'";
val _ = out "sip_type_naOut" "na'";
