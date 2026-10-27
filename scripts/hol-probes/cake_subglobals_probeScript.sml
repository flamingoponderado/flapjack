load "preamble"; load "source_to_flatProofTheory";
open HolKernel Parse boolLib bossLib preamble;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
val _ = (print "subglobals_type="; print_type (type_of ``source_to_flatProof$subglobals``); print "\n");
val _ = (print "subglobals_definition="; print_thm source_to_flatProofTheory.subglobals_def; print "\n");
val _ = (print "submap_fresh="; print_thm source_to_flatProofTheory.submap_distinct_fupdate_flookup; print "\n");
val _ = (print "submap_update="; print_thm source_to_flatProofTheory.submap_fupdate_flookup; print "\n");
val refl = prove (``∀g : 'a option list. source_to_flatProof$subglobals g g``,
  simp [source_to_flatProofTheory.subglobals_def]);
val _ = (print "refl_replay="; print_thm refl; print "\n");
val trans = prove (``∀g1 g2 g3 : 'a option list.
  source_to_flatProof$subglobals g1 g2 ∧ source_to_flatProof$subglobals g2 g3 ⇒
  source_to_flatProof$subglobals g1 g3``,
  rw [source_to_flatProofTheory.subglobals_def] >> res_tac >> fs []);
val _ = (print "trans_replay="; print_thm trans; print "\n");
fun capture label term = (print (label ^ "="); print_term (rhs (concl (EVAL term))); print "\n");
val _ = capture "empty" ``source_to_flatProof$subglobals [] [SOME (1:num)]``;
val _ = capture "fill_empty" ``source_to_flatProof$subglobals [SOME (1:num); NONE] [SOME 1; SOME 2]``;
val _ = capture "append" ``source_to_flatProof$subglobals [SOME (1:num); NONE] [SOME 1; SOME 2; SOME 3]``;
val _ = capture "shorter" ``source_to_flatProof$subglobals [NONE; NONE] [NONE] : bool``;
val _ = capture "overwrite" ``source_to_flatProof$subglobals [SOME (1:num); NONE] [SOME 2; NONE]``;
val _ = capture "remove" ``source_to_flatProof$subglobals [SOME (1:num)] [NONE]``;
