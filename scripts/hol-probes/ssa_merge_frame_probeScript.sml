load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory word_allocTheory sptreeTheory reg_allocTheory;
val _ = Globals.linewidth := 1000;
val ssa_map_ok_extend = GEN_ALL (prove (``ssa_map_ok na ssa ∧
  ¬is_phy_var na ⇒
  ssa_map_ok (na+4) (insert h na ssa)``, full_simp_tac(srw_ss())[ssa_map_ok_def]>>
  srw_tac[][]>>full_simp_tac(srw_ss())[lookup_insert]>>
  Cases_on`x=h`>>full_simp_tac(srw_ss())[]>>
  res_tac>-
    DECIDE_TAC));
val frame_source = prove (``  ∀ls na ssaL ssaR.
  is_alloc_var na
  ⇒
  let(moveL,moveR,na',ssaL',ssaR') = merge_moves ls ssaL ssaR na in
  is_alloc_var na' ∧
  na ≤ na' ∧
  (ssa_map_ok na ssaL ⇒ ssa_map_ok na' ssaL') ∧
  (ssa_map_ok na ssaR ⇒ ssa_map_ok na' ssaR')``,
  Induct>>full_simp_tac(srw_ss())[merge_moves_def]>-
    (srw_tac[][]>>full_simp_tac(srw_ss())[])
  >>
  rpt strip_tac>>
  full_simp_tac(srw_ss())[LET_THM]>>
  last_x_assum(qspecl_then[`na`,`ssaL`,`ssaR`] assume_tac)>>
  rev_full_simp_tac(srw_ss())[]>>
  Cases_on`merge_moves ls ssaL ssaR na`>>PairCases_on`r`>>rev_full_simp_tac(srw_ss())[]>>
  EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
  (CONJ_TAC>-
    (full_simp_tac(srw_ss())[is_alloc_var_def]>>
    (assume_tac arithmeticTheory.MOD_PLUS>>full_simp_tac(srw_ss())[]>>
    pop_assum (qspecl_then [`4`,`r1`,`4`] assume_tac)>>
    rev_full_simp_tac(srw_ss())[]))
  >>
  CONJ_TAC>-
    DECIDE_TAC)
  >>
  metis_tac[ssa_map_ok_extend,convention_partitions]);
val _ = (print "mf_full_source_replay=";print_thm frame_source;print "\n");
fun out label q = (print(label ^ "="); print_term(rconc(EVAL q)); print "\n");
val _ = out "mf_empty" ``merge_moves [] (fromAList [(1,7)]) (fromAList [(1,9)]) 5``;
val _ = out "mf_missing_both" ``merge_moves [1] LN LN 5``;
val _ = out "mf_missing_left" ``merge_moves [1] LN (fromAList [(1,9)]) 5``;
val _ = out "mf_missing_right" ``merge_moves [1] (fromAList [(1,7)]) LN 5``;
val _ = out "mf_equal" ``merge_moves [1] (fromAList [(1,7)]) (fromAList [(1,7)]) 5``;
val _ = out "mf_unequal" ``merge_moves [1] (fromAList [(1,7)]) (fromAList [(1,9)]) 5``;
val _ = out "mf_tail_order" ``merge_moves [0;2] (fromAList [(0,7);(2,11)]) (fromAList [(0,9);(2,13)]) 5``;
val _ = out "mf_duplicate" ``merge_moves [1;1] (fromAList [(1,7)]) (fromAList [(1,9)]) 5``;
val _ = out "mf_invalid" ``merge_moves [0;4] (BN LN LN:num num_map) (fromAList [(0,7);(4,9)]) 0``;
val _ = out "mf_big" ``merge_moves [0] (LS 18446744073709551616) (LS 3) 18446744073709551616``;
