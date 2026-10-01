load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory sptreeTheory reg_allocTheory wordSemTheory;
val ignore_source = GEN_ALL (prove (``ssa_map_ok na ssa ∧
  ssa_locals_rel na ssa stloc cstloc ∧
  is_phy_var v
  ⇒
  ssa_locals_rel na ssa stloc (insert v a cstloc)``, srw_tac[][ssa_locals_rel_def,ssa_map_ok_def,set_var_def]>>
  full_simp_tac(srw_ss())[lookup_insert]>-
    metis_tac[]
  >>
  res_tac>>
  full_simp_tac(srw_ss())[domain_lookup]>>
  metis_tac[]));

fun out label goal = let
 val th = PART_MATCH (snd o strip_imp) ignore_source goal
 val premise = fst(dest_imp(concl th))
 val hp = prove(premise, rw [ssa_map_ok_def,ssa_locals_rel_def,lookup_def,lookup_insert,domain_lookup,is_alloc_var_def,is_phy_var_def] >> EVERY_CASE_TAC >> fs [lookup_def,lookup_insert] >> EVERY_CASE_TAC >> fs [lookup_def,lookup_insert])
 val result = MATCH_MP th hp
 val _ = if null(hyp result) andalso aconv(concl result) goal then () else raise Fail "wrong original application"
 in print(label ^ "=");print_term(rhs(concl(EQT_INTRO result)));print "\n" end;
val _ = out "pi_empty" ``ssa_locals_rel 8 (LN:num num_map) (LN:bool num_map) (insert 0 T (LN:bool num_map))``;
val _ = out "pi_empty_existing" ``ssa_locals_rel 8 (LN:num num_map) (LN:bool num_map) (insert 2 F (LS T:bool num_map))``;
val _ = out "pi_live" ``ssa_locals_rel 8 (LS 1:num num_map) (LS T:bool num_map) (insert 0 F (BN LN (LS T):bool num_map))``;
val _ = out "pi_overwrite" ``ssa_locals_rel 8 (LS 1:num num_map) (LS T:bool num_map) (insert 0 T (BS LN F (LS T):bool num_map))``;
val _ = out "pi_branch" ``ssa_locals_rel 8 (LS 1:num num_map) (LS T:bool num_map) (insert 2 T (BS (LS F) F (LS T):bool num_map))``;
val _ = out "pi_invalid" ``ssa_locals_rel 8 (BN LN LN:num num_map) (BN LN LN:bool num_map) (insert 0 T (BN LN LN:bool num_map))``;
val _ = out "pi_huge" ``ssa_locals_rel 8 (LS 1:num num_map) (LS T:bool num_map) (insert 1000000000000000000000000000000 F (BN LN (LS T):bool num_map))``;
val _ = out "pi_generic_nat" ``ssa_locals_rel 8 (LS 1:num num_map) (LS 99:num num_map) (insert 0 777 (BN LN (LS 99):num num_map))``;
val _ = (print "pi_nonphysical_guard=";print_term(rconc(EVAL ``is_phy_var 1``));print "\n");
val _ = (print "pi_invalid_map_guard=";print_term(rconc(SIMP_CONV (srw_ss()) [ssa_map_ok_def,lookup_def,is_phy_var_def] ``ssa_map_ok 8 (LS 0)``));print "\n");
val _ = (print "pi_full_source_replay=";print_thm ignore_source;print "\n");
val _ = (print "pi_original_types="; app (fn v => (print_term v; print ":"; print_type(type_of v); print ";")) (fst(strip_forall(concl ignore_source))); print "\n");
