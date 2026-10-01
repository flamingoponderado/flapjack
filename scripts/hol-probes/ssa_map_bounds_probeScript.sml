load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory sptreeTheory reg_allocTheory;
fun out label q =
  let val unfolded = (rconc(ONCE_REWRITE_CONV [insert_def] q) handle UNCHANGED => q)
  in print(label ^ "=");
     print_term(rconc(SIMP_CONV (srw_ss()) [ssa_map_ok_def,lookup_def,is_phy_var_def] unfolded));
     print "\n"
  end;
val _ = out "mb_empty" ``(ssa_map_ok 0 (LN:num num_map),ssa_map_ok 17 LN)``;
val _ = out "mb_valid" ``(ssa_map_ok 8 (LS 7),ssa_map_ok 12 (LS 7))``;
val _ = out "mb_same" ``(ssa_map_ok 8 (LS 7),ssa_map_ok 8 (LS 7))``;
val _ = out "mb_bound" ``(ssa_map_ok 7 (LS 7),ssa_map_ok 8 (LS 7))``;
val _ = out "mb_physical" ``(ssa_map_ok 100 (LS 2),ssa_map_ok 200 (LS 2))``;
val _ = out "mb_invalid" ``(ssa_map_ok 0 (BN LN LN:num num_map),ssa_map_ok 1 (BN LN LN:num num_map))``;
val _ = out "mb_large_physical" ``(ssa_map_ok 18446744073709551624 (LS 18446744073709551620),ssa_map_ok 18446744073709551632 (LS 18446744073709551620))``;
val _ = out "mb_large" ``(ssa_map_ok 18446744073709551624 (LS 18446744073709551621),ssa_map_ok 18446744073709551632 (LS 18446744073709551621))``;
val _ = out "mb_overwrite" ``(ssa_map_ok 8 (insert 0 7 (LS 2)),ssa_map_ok 12 (insert 0 7 (LS 2)))``;
val more = Q.prove(
 `!na ssa na'. ssa_map_ok na ssa /\ na <= na' ==> ssa_map_ok na' ssa`,
 full_simp_tac(srw_ss())[ssa_map_ok_def]>>srw_tac[][] >-
 metis_tac[] >> res_tac >> full_simp_tac(srw_ss())[] >> DECIDE_TAC);
val _ = (print "mb_more=";print_thm more;print "\n");
