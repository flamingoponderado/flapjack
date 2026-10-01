load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory sptreeTheory reg_allocTheory;
val ssa_map_ok_inter_source = GEN_ALL (prove (``ssa_map_ok na ssa ⇒
  ssa_map_ok na (inter ssa ssa')``, full_simp_tac(srw_ss())[ssa_map_ok_def,lookup_inter]>>srw_tac[][]>>EVERY_CASE_TAC>>
  full_simp_tac(srw_ss())[]>>
  metis_tac[]));
val ssa_map_ok_insert_source = GEN_ALL (prove (``ssa_map_ok na ssa ∧
  y < na ∧ ¬is_phy_var y ⇒
  ssa_map_ok na (insert x y ssa)``, rw[ssa_map_ok_def,lookup_insert]>>
  pop_assum mp_tac>>rw[]>>
  metis_tac[]));

fun out label theorem goal = let
 val th = PART_MATCH (snd o strip_imp) theorem goal
 val premise = fst (dest_imp (concl th))
 val hp = prove (premise, rw [ssa_map_ok_def,lookup_def,is_phy_var_def] >> EVERY_CASE_TAC >> fs [lookup_def,is_phy_var_def] >> EVERY_CASE_TAC >> fs [lookup_def,is_phy_var_def])
 val result = MATCH_MP th hp
 val _ = if null(hyp result) andalso aconv(concl result) goal then () else raise Fail "wrong original application"
 in print(label ^ "="); print_term(rhs(concl(EQT_INTRO result))); print "\n" end;
val _ = out "mi_empty" ssa_map_ok_inter_source ``ssa_map_ok 8 (inter (LN:num num_map) (LS T:bool num_map))``;
val _ = out "mi_retain_alloc" ssa_map_ok_inter_source ``ssa_map_ok 8 (inter (LS 1:num num_map) (LS T:bool num_map))``;
val _ = out "mi_retain_stack" ssa_map_ok_inter_source ``ssa_map_ok 8 (inter (LS 7:num num_map) (LS F:bool num_map))``;
val _ = out "mi_drop" ssa_map_ok_inter_source ``ssa_map_ok 8 (inter (LS 7:num num_map) (LN:bool num_map))``;
val _ = out "mi_invalid" ssa_map_ok_inter_source ``ssa_map_ok 8 (inter (BN LN LN:num num_map) (BS LN T LN:bool num_map))``;
val _ = out "mi_branch" ssa_map_ok_inter_source ``ssa_map_ok 8 (inter (BS (LS 1) 3 (LS 7):num num_map) (BS LN T (LS F):bool num_map))``;
val _ = out "mi_huge" ssa_map_ok_inter_source ``ssa_map_ok 1000000000000000000000000000004 (inter (LS 1000000000000000000000000000003:num num_map) (LS T:bool num_map))``;
val _ = out "ms_empty" ssa_map_ok_insert_source ``ssa_map_ok 8 (insert 0 1 (LN:num num_map))``;
val _ = out "ms_stack" ssa_map_ok_insert_source ``ssa_map_ok 8 (insert 2 7 (LN:num num_map))``;
val _ = out "ms_overwrite" ssa_map_ok_insert_source ``ssa_map_ok 8 (insert 0 3 (LS 1:num num_map))``;
val _ = out "ms_extend" ssa_map_ok_insert_source ``ssa_map_ok 8 (insert 2 5 (LS 7:num num_map))``;
val _ = out "ms_invalid" ssa_map_ok_insert_source ``ssa_map_ok 8 (insert 2 1 (BN LN LN:num num_map))``;
val _ = out "ms_huge" ssa_map_ok_insert_source ``ssa_map_ok 1000000000000000000000000000004 (insert 1000000000000000000000000000000 1000000000000000000000000000003 (LS 7:num num_map))``;
val _ = (print "ms_physical_guard="; print_term(rconc(EVAL ``~is_phy_var 2``)); print "\n");
val _ = (print "ms_bound_guard="; print_term(rconc(EVAL ``8 < (8:num)``)); print "\n");
val _ = (print "ssa_map_ok_inter_source_replay="; print_thm ssa_map_ok_inter_source; print "\n");
val _ = (print "ssa_map_ok_insert_source_replay="; print_thm ssa_map_ok_insert_source; print "\n");
val _ = (print "mi_original_types="; app (fn v => (print_term v; print ":"; print_type(type_of v); print ";")) (fst(strip_forall(concl ssa_map_ok_inter_source))); print "\n");
