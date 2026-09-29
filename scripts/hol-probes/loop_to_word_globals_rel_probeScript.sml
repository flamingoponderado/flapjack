(* Direct HOL EVAL observations for loop_to_wordProof$globals_rel_def. *)
load "bossLib";
load "preamble";
load "loop_to_wordProofTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open loop_to_wordProofTheory;

fun print_eval label q =
  let
    val th = SIMP_CONV (srw_ss())
      [globals_rel_def, FLOOKUP_UPDATE, FLOOKUP_EMPTY] q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val source_match =
  ``((FEMPTY : (5 word, 64 word_loc) fmap) |+
      ((1w : 5 word), Word (9w : 64 word)))``;
val target_match =
  ``((FEMPTY : (stackLang$store_name, 64 word_loc) fmap) |+
      (stackLang$Temp (1w : 5 word), Word (9w : 64 word)))``;
val target_different_value =
  ``((FEMPTY : (stackLang$store_name, 64 word_loc) fmap) |+
      (stackLang$Temp (1w : 5 word), Word (10w : 64 word)))``;
val target_different_key =
  ``((FEMPTY : (stackLang$store_name, 64 word_loc) fmap) |+
      (stackLang$Temp (2w : 5 word), Word (9w : 64 word)))``;
val source_empty = ``(FEMPTY : (5 word, 64 word_loc) fmap)``;

val _ = print_eval "globals_rel_match"
  ``globals_rel ^source_match ^target_match``;
val _ = print_eval "globals_rel_value_mismatch"
  ``globals_rel ^source_match ^target_different_value``;
val _ = print_eval "globals_rel_temp_mismatch"
  ``globals_rel ^source_match ^target_different_key``;
val _ = print_eval "globals_rel_empty_source"
  ``globals_rel ^source_empty ^target_different_key``;
