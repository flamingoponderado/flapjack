load "preamble"; load "source_to_flatProofTheory";
open HolKernel Parse boolLib bossLib preamble;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
val _ = (print "subglobals_type="; print_type (type_of ``source_to_flatProof$subglobals``); print "\n");
val _ = (print "subglobals_definition="; print_thm source_to_flatProofTheory.subglobals_def; print "\n");
val _ = (print "submap_fresh="; print_thm source_to_flatProofTheory.submap_distinct_fupdate_flookup; print "\n");
val _ = (print "submap_update="; print_thm source_to_flatProofTheory.submap_fupdate_flookup; print "\n");
val _ = (print "subglobals_none="; print_thm source_to_flatProofTheory.subglobals_NONE; print "\n");
val _ = (print "subglobals_add_none="; print_thm source_to_flatProofTheory.subglobals_add_NONE; print "\n");
val _ = (print "idx_kind_type="; print_type (type_of ``source_to_flatProof$Idx_Var``); print "\n");
val _ = (print "idx_prev="; print_thm source_to_flatProofTheory.idx_prev_def; print "\n");
val _ = (print "idx_prev_refl="; print_thm source_to_flatProofTheory.idx_prev_refl; print "\n");
val _ = (print "idx_prev_trans="; print_thm source_to_flatProofTheory.idx_prev_trans; print "\n");
val _ = (print "idx_block="; print_thm source_to_flatProofTheory.idx_block_def; print "\n");
val _ = (print "idx_final_block="; print_thm source_to_flatProofTheory.idx_final_block_def; print "\n");
val _ = (print "idx_allocated="; print_thm source_to_flatProofTheory.genv_allocated_idxs_def; print "\n");
val _ = (print "idx_disjoint="; print_thm source_to_flatProofTheory.ALL_DISJOINT_DEF; print "\n");
val _ = (print "idx_finish="; print_thm source_to_flatProofTheory.fin_idx_match_def; print "\n");
val _ = (print "orac_next_inner="; print_thm source_to_flatProofTheory.src_orac_next_cfg_inner_def; print "\n");
val _ = (print "orac_next="; print_thm source_to_flatProofTheory.src_orac_next_cfg_def; print "\n");
val _ = (print "idx_range="; print_thm source_to_flatProofTheory.idx_range_rel_def; print "\n");
val _ = (print "idx_blank="; print_thm source_to_flatProofTheory.idx_range_rel_v_REPLICATE_NONE; print "\n");
val refl = prove (``∀g : 'a option list. source_to_flatProof$subglobals g g``,
  simp [source_to_flatProofTheory.subglobals_def]);
val _ = (print "refl_replay="; print_thm refl; print "\n");
val trans = prove (``∀g1 g2 g3 : 'a option list.
  source_to_flatProof$subglobals g1 g2 ∧ source_to_flatProof$subglobals g2 g3 ⇒
  source_to_flatProof$subglobals g1 g3``,
  rw [source_to_flatProofTheory.subglobals_def] >> res_tac >> fs []);
val _ = (print "trans_replay="; print_thm trans; print "\n");
val append_replay = prove (``∀g1 g2 g3 : 'a option list.
    source_to_flatProof$subglobals (g1 ++ g2) (g1 ++ g3) = source_to_flatProof$subglobals g2 g3 ∧
    (LENGTH g2 = LENGTH g3 ⇒
      source_to_flatProof$subglobals (g2 ++ g1) (g3 ++ g1) = source_to_flatProof$subglobals g2 g3)``,
  rw [source_to_flatProofTheory.subglobals_def] >> eq_tac >> rw []
  >- (first_x_assum (qspec_then `n + LENGTH (g1:'a option list)` mp_tac) >> rw [EL_APPEND_EQN])
  >- (first_x_assum (qspec_then `n - LENGTH (g1:'a option list)` mp_tac) >> rw [EL_APPEND_EQN] >> fs [EL_APPEND_EQN])
  >- (first_x_assum (qspec_then `n` mp_tac) >> rw [EL_APPEND_EQN])
  >- (Cases_on `n < LENGTH g3` >> fs [EL_APPEND_EQN] >> rfs [] >> fs []));
val _ = (print "append_replay="; print_thm append_replay; print "\n");
fun capture label term = (print (label ^ "="); print_term (rhs (concl (EVAL term))); print "\n");
val _ = capture "empty" ``source_to_flatProof$subglobals [] [SOME (1:num)]``;
val _ = capture "fill_empty" ``source_to_flatProof$subglobals [SOME (1:num); NONE] [SOME 1; SOME 2]``;
val _ = capture "append" ``source_to_flatProof$subglobals [SOME (1:num); NONE] [SOME 1; SOME 2; SOME 3]``;
val _ = capture "shorter" ``source_to_flatProof$subglobals [NONE; NONE] [NONE] : bool``;
val _ = capture "overwrite" ``source_to_flatProof$subglobals [SOME (1:num); NONE] [SOME 2; NONE]``;
val _ = capture "remove" ``source_to_flatProof$subglobals [SOME (1:num)] [NONE]``;
