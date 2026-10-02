(* Original HOL alignment (alignmentScript.sml:18-29) and words word_slice (wordsScript.sml:238):
   types and EVAL results of word_slice, align and aligned on small words, including a slice
   bound above ^HB and an alignment exponent at least the width, and byte_align/byte_aligned at
   64 bits proved through LOG2 8 = 3 (LOG2 is [nocompute]). *)
load "bossLib";
load "alignmentTheory";
load "wordsLib";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 4000;
fun observe label term = let val th = EVAL term in print (label ^ "="); print_term (rhs (concl th)); print "\n" end;
fun observe_type label term = (print (label ^ "="); print_type (type_of term); print "\n");
fun observe_thm label th = (print (label ^ "="); print_term (concl th); print "\n");
val _ = observe_type "al_align_type" ``alignment$align``;
val _ = observe_type "al_byte_align_type" ``alignment$byte_align``;
val _ = observe "al_slice_7_4" ``word_slice 7 4 (0xABCDw : word16)``;
val _ = observe "al_slice_20_4" ``word_slice 20 4 (0xABCDw : word16)``;
val _ = observe "al_slice_3_9" ``word_slice 3 9 (0xABCDw : word16)``;
val _ = observe "al_align_3" ``align 3 (0x12345w : word32)``;
val _ = observe "al_align_0" ``align 0 (0x12345w : word32)``;
val _ = observe "al_align_40" ``align 40 (0x12345w : word32)``;
val _ = observe "al_aligned_t" ``aligned 2 (12w : word8)``;
val _ = observe "al_aligned_f" ``aligned 2 (13w : word8)``;
val log2_8 = prove (``LOG2 8 = 3``, REWRITE_TAC [bitTheory.LOG2_def] >> irule logrootTheory.LOG_UNIQUE >> EVAL_TAC);
val _ = observe_thm "al_byte_align_64" (prove (``byte_align (0x1234567w : word64) = 0x1234560w``,
  REWRITE_TAC [alignmentTheory.byte_align_def] >> CONV_TAC (DEPTH_CONV wordsLib.SIZES_CONV) >> SIMP_TAC arith_ss [log2_8] >> EVAL_TAC));
val _ = observe_thm "al_byte_aligned_64" (prove (``byte_aligned (16w : word64)``,
  REWRITE_TAC [alignmentTheory.byte_aligned_def] >> CONV_TAC (DEPTH_CONV wordsLib.SIZES_CONV) >> SIMP_TAC arith_ss [log2_8] >> EVAL_TAC));
