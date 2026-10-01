load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory sptreeTheory reg_allocTheory;
val extend_source = GEN_ALL (prove (``ssa_map_ok na ssa ∧
  ¬is_phy_var na ⇒
  ssa_map_ok (na+4) (insert h na ssa)``, full_simp_tac(srw_ss())[ssa_map_ok_def]>>
  srw_tac[][]>>full_simp_tac(srw_ss())[lookup_insert]>>
  Cases_on`x=h`>>full_simp_tac(srw_ss())[]>>
  res_tac>-
    DECIDE_TAC));
fun out label goal = let
 val th = PART_MATCH (snd o strip_imp) extend_source goal
 val premise = fst (dest_imp (concl th))
 val hp = prove (premise, simp [ssa_map_ok_def,lookup_def,is_phy_var_def])
 val result = MATCH_MP th hp
 val _ = if null (hyp result) andalso aconv (concl result) goal then () else raise Fail "wrong/undischarged original application"
 in print(label ^ "=");print_term(rhs(concl(EQT_INTRO result)));print "\n" end;
val _ = out "se_empty_alloc" ``ssa_map_ok (1+4) (insert 0 1 (LN:num num_map))``;
val _ = out "se_empty_stack" ``ssa_map_ok (3+4) (insert 0 3 (LN:num num_map))``;
val _ = out "se_existing" ``ssa_map_ok (9+4) (insert 9 9 (LS 7:num num_map))``;
val _ = out "se_overwrite" ``ssa_map_ok (9+4) (insert 0 9 (LS 7:num num_map))``;
val _ = out "se_invalid" ``ssa_map_ok (1+4) (insert 2 1 (BN LN LN:num num_map))``;
val _ = out "se_huge_alloc" ``ssa_map_ok (1000000000000000000000000000001+4) (insert 1000000000000000000000000000000 1000000000000000000000000000001 (LN:num num_map))``;
val _ = out "se_huge_stack" ``ssa_map_ok (1000000000000000000000000000003+4) (insert 0 1000000000000000000000000000003 (LN:num num_map))``;
val _ = (print "se_physical_premise=";print_term(rconc(EVAL ``~is_phy_var 2``));print "\n");
val _ = (print "se_at_bound_premise=";print_term(rconc(SIMP_CONV (srw_ss()) [ssa_map_ok_def,lookup_def,is_phy_var_def] ``ssa_map_ok 7 (LS 7)``));print "\n");
val _ = (print "se_full_source_replay=";print_thm extend_source;print "\n");
