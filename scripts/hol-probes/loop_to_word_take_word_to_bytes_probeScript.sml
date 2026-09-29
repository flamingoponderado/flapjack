(*
  Direct HOL oracle for loop_to_wordProof$TAKE_1_word_to_bytes
  (cakeml/pancake/proofs/loop_to_wordProofScript.sml:1449-1451):

    Theorem TAKE_1_word_to_bytes:
      good_dimindex(:'a) ⇒ TAKE 1 (word_to_bytes (w:'a word) F) = [get_byte 0w w F]

  The rows print the proved source statement and the HOL-EVAL result of both
  sides at the 32- and 64-bit dimensions that `good_dimindex` admits.  The
  kernel-checked Lean replay is
  Flapjack.Test.LoopToWordTakeWordToBytesParity.
*)
load "bossLib";
load "preamble";
load "loop_to_wordTheory";
load "loop_to_wordProofTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open loop_to_wordProofTheory;

fun print_eval label q =
  let val th = EVAL q in
    print (label ^ "="); print_term (rconc th); print "\n"
  end;

fun print_conclusion label th =
  (print (label ^ "="); print_term (concl th); print "\n");

val _ = print_conclusion "take1_statement" (TAKE_1_word_to_bytes);

val _ = print_eval "twb32_0" ``TAKE 1 (word_to_bytes (0w:32 word) F)``;
val _ = print_eval "twb32_1" ``TAKE 1 (word_to_bytes (1w:32 word) F)``;
val _ = print_eval "twb32_hi" ``TAKE 1 (word_to_bytes (0xABw:32 word) F)``;
val _ = print_eval "gb32_0" ``[get_byte (0w:32 word) (0w:32 word) F]``;
val _ = print_eval "gb32_1" ``[get_byte (0w:32 word) (1w:32 word) F]``;
val _ = print_eval "gb32_hi" ``[get_byte (0w:32 word) (0xABw:32 word) F]``;

val _ = print_eval "twb64_0" ``TAKE 1 (word_to_bytes (0w:64 word) F)``;
val _ = print_eval "twb64_1" ``TAKE 1 (word_to_bytes (1w:64 word) F)``;
val _ = print_eval "twb64_hi" ``TAKE 1 (word_to_bytes (0xABw:64 word) F)``;
val _ = print_eval "gb64_0" ``[get_byte (0w:64 word) (0w:64 word) F]``;
val _ = print_eval "gb64_1" ``[get_byte (0w:64 word) (1w:64 word) F]``;
val _ = print_eval "gb64_hi" ``[get_byte (0w:64 word) (0xABw:64 word) F]``;
