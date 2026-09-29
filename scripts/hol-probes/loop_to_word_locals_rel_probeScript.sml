(*
  Direct HOL proof observations for loop_to_wordProof$locals_rel_def
  (cakeml/pancake/proofs/loop_to_wordProofScript.sml:19-24).  The relation
  quantifies over all source names, so each row is discharged from the HOL
  definition rather than treated as a closed executable term.
*)
load "bossLib";
load "preamble";
load "loop_to_wordTheory";
load "loop_to_wordProofTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open loop_to_wordTheory;
open loop_to_wordProofTheory;

fun print_eval label q =
  let val th = EVAL q in
    print (label ^ "="); print_term (rconc th); print "\n"
  end;

fun print_conclusion label th =
  (print (label ^ "="); print_term (concl th); print "\n");

val ctxt = ``insert 0 4 (LN : num num_map)``;
val src = ``insert 0 (Word 7w) (LN : 64 word_loc num_map)``;
val dst = ``insert 4 (Word 7w) (insert 6 (Loc 1 2) (LN : 64 word_loc num_map))``;
val odd_ctxt = ``insert 0 3 (LN : num num_map)``;
val odd_dst = ``insert 3 (Word 7w) (LN : 64 word_loc num_map)``;
val zero_ctxt = ``insert 0 0 (LN : num num_map)``;
val zero_dst = ``insert 0 (Word 7w) (LN : 64 word_loc num_map)``;
val noninjective_ctxt = ``insert 1 4 (insert 0 4 (LN : num num_map))``;
val noninjective_src = ``insert 0 (Word 7w) (insert 1 (Word 8w) (LN : 64 word_loc num_map))``;
val missing_src = ``insert 2 (Word 7w) (LN : 64 word_loc num_map)``;
val wrong_dst = ``insert 4 (Word 8w) (LN : 64 word_loc num_map)``;

fun prove_row label goal =
  let
    val _ = prove(goal,
      srw_tac[][locals_rel_def, INJ_DEF, find_var_def, domain_lookup,
        lookup_insert])
  in
    print (label ^ "=T\n")
  end;

fun refute_row label goal =
  let
    val _ = prove(goal,
      srw_tac[][locals_rel_def, INJ_DEF, find_var_def, domain_lookup,
        lookup_insert] >> metis_tac [])
  in
    print (label ^ "=F\n")
  end;

prove_row "lt_locals_rel_good_with_extra_target" ``locals_rel ^ctxt ^src ^dst``;
refute_row "lt_locals_rel_odd_register" ``~locals_rel ^odd_ctxt ^src ^odd_dst``;
refute_row "lt_locals_rel_zero_register" ``~locals_rel ^zero_ctxt ^src ^zero_dst``;
val _ = prove(
  ``~locals_rel ^noninjective_ctxt ^noninjective_src
      (insert 4 (Word 7w) (LN : 64 word_loc num_map))``,
  srw_tac[][locals_rel_def, INJ_DEF, find_var_def, domain_lookup,
    lookup_insert] >> DISJ1_TAC >>
  qexists_tac `0` >> qexists_tac `1` >>
  simp [find_var_def, lookup_insert]);
print "lt_locals_rel_noninjective=F\n";
refute_row "lt_locals_rel_missing_context" ``~locals_rel ^ctxt ^missing_src ^dst``;
refute_row "lt_locals_rel_wrong_value" ``~locals_rel ^ctxt ^src ^wrong_dst``;

val inserted_src = ``insert 0 (Word 9w) ^src``;
val inserted_dst = ``insert 4 (Word 9w) ^dst``;
prove_row "lt_locals_rel_insert_mapped" ``locals_rel ^ctxt ^inserted_src ^inserted_dst``;
val unmapped_dst = ``insert 6 (Word 9w) ^dst``;
prove_row "lt_locals_rel_insert_unmapped" ``locals_rel ^ctxt ^src ^unmapped_dst``;
refute_row "lt_locals_rel_insert_unmapped_collision"
  ``~locals_rel ^ctxt ^src (insert 4 (Word 9w) ^dst)``;

(* Exact source theorem statements, followed by direct evaluator observations. *)
print_conclusion "locals_rel_get_var_statement" locals_rel_get_var;
print_conclusion "locals_rel_get_vars_statement" locals_rel_get_vars;

val lookup_src = ``insert 2 (Word 9w) (insert 1 (Word 7w) (LN : 64 word_loc num_map))``;
val lookup_dst = ``insert 6 (Word 9w) (insert 4 (Word 7w) (LN : 64 word_loc num_map))``;
val loop_state = ``(s:(64,unit) loopSem$state) with locals := ^lookup_src``;
val word_state = ``(t:(64,unit,unit) wordSem$state) with locals := ^lookup_dst``;
print_eval "loop_get_vars_hit" ``loopSem$get_vars [1;2] ^loop_state``;
print_eval "loop_get_vars_miss" ``loopSem$get_vars [1;3] ^loop_state``;
print_eval "word_get_vars_hit" ``wordSem$get_vars [4;6] ^word_state``;
print_eval "word_get_vars_miss" ``wordSem$get_vars [4;5] ^word_state``;
