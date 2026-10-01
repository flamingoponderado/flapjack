load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory sptreeTheory reg_allocTheory;
val ssa_map_ok_more = prove(``ssa_map_ok na ssa ∧ na ≤ na' ⇒
  ssa_map_ok na' ssa``,
full_simp_tac(srw_ss())[ssa_map_ok_def]>>srw_tac[][]
  >-
    metis_tac[]>>
  res_tac>>full_simp_tac(srw_ss())[]>>DECIDE_TAC);
val result = Q.prove(`ssa_map_ok na ssa ==> ssa_map_ok (na+2) ssa`,
 metis_tac[ssa_map_ok_more, DECIDE``na:num <= na+2``]);
val _ = print "ml_full="; val _ = print_thm result; val _ = print "\n";
fun out label q = (print(label ^ "=");print_term(rconc(SIMP_CONV (srw_ss()) [ssa_map_ok_def,lookup_def,is_phy_var_def] q));print "\n");
val _ = out "ml_empty" ``(ssa_map_ok 0 (LN:num num_map),ssa_map_ok (0+2) LN)``;
val _ = out "ml_valid" ``(ssa_map_ok 8 (LS 7),ssa_map_ok (8+2) (LS 7))``;
val _ = out "ml_rejected" ``(ssa_map_ok 7 (LS 7),ssa_map_ok (7+2) (LS 7))``;
val _ = out "ml_physical" ``(ssa_map_ok 100 (LS 2),ssa_map_ok (100+2) (LS 2))``;
val _ = out "ml_invalid" ``(ssa_map_ok 0 (BN LN LN:num num_map),ssa_map_ok (0+2) (BN LN LN))``;
val _ = out "ml_large" ``(ssa_map_ok 18446744073709551624 (LS 18446744073709551621),ssa_map_ok (18446744073709551624+2) (LS 18446744073709551621))``;
