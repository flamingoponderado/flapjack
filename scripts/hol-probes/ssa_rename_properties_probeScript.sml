load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory word_allocTheory sptreeTheory reg_allocTheory;
val is_alloc_var_add = prove (``!na. is_alloc_var na ==> is_alloc_var (na+4)``, full_simp_tac(srw_ss())[is_alloc_var_def] >> (qspec_then `4` assume_tac arithmeticTheory.MOD_PLUS >> full_simp_tac(srw_ss())[] >> pop_assum (qspecl_then [`na`,`4`] assume_tac) >> rev_full_simp_tac(srw_ss())[]));
val is_stack_var_add = prove (``!na. is_stack_var na ==> is_stack_var (na+4)``, full_simp_tac(srw_ss())[is_stack_var_def] >> (qspec_then `4` assume_tac arithmeticTheory.MOD_PLUS >> full_simp_tac(srw_ss())[] >> pop_assum (qspecl_then [`na`,`4`] assume_tac) >> rev_full_simp_tac(srw_ss())[]));
val props_source = prove (``∀ls ssa na ls' ssa' na'.
  list_next_var_rename ls ssa na = (ls',ssa',na') ==>
  (is_alloc_var na ∨ is_stack_var na) ∧
  ssa_map_ok na ssa
  ⇒
  na ≤ na' ∧
  (is_alloc_var na ⇒ is_alloc_var na') ∧
  (is_stack_var na ⇒ is_stack_var na') ∧
  ssa_map_ok na' ssa'``, Induct>>full_simp_tac(srw_ss())[list_next_var_rename_def,next_var_rename_def]>>
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
fun out label q = let
  val eq = EVAL q
  val (xs,rest) = dest_pair (rhs (concl eq))
  val (tree,next) = dest_pair rest
  val (_,args) = strip_comb q
  val specialized = SPECL (args @ [xs,tree,next]) props_source
  val first = MATCH_MP specialized eq
  val premise = fst (dest_imp (concl first))
  val hp = prove (premise, simp [ssa_map_ok_def,lookup_def,is_alloc_var_def,is_stack_var_def,is_phy_var_def])
  val result = MATCH_MP first hp
  val _ = if null (hyp result) then () else raise Fail "undischarged source premise"
  (* EQT_INTRO converts the PROVED four-conjunct conclusion to T; it does not assume it. *)
  val verified = rhs (concl (EQT_INTRO result))
  in print(label ^ "=");print_term(mk_pair(next,verified));print "\n" end;
val _ = out "rp_empty_alloc" ``list_next_var_rename [] (LN:num num_map) 1``;
val _ = out "rp_empty_stack" ``list_next_var_rename [] (LN:num num_map) 3``;
val _ = out "rp_alloc_duplicates" ``list_next_var_rename [9;9;2] (LN:num num_map) 1``;
val _ = out "rp_stack_duplicates" ``list_next_var_rename [9;9;2] (LN:num num_map) 3``;
val _ = out "rp_existing" ``list_next_var_rename [9;1] (LS 7:num num_map) 9``;
val _ = out "rp_overwrite" ``list_next_var_rename [0;0] (LS 7:num num_map) 9``;
val _ = out "rp_invalid" ``list_next_var_rename [2;2] (BN LN LN:num num_map) 1``;
val _ = out "rp_huge" ``list_next_var_rename [1000000000000000000000000000000;0;0] (LN:num num_map) 1000000000000000000000000000001``;
val _ = (print "rp_full_source_replay=";print_thm props_source;print "\n");
