load "bossLib";
load "preamble";
load "lab_to_targetProofTheory";
open bossLib HolKernel Parse preamble lab_to_targetProofTheory lab_to_targetTheory labPropsTheory labSemTheory asmTheory;
val _ = show_types := true;
fun capture label th = (print(label ^ "="); print_term(concl th); print "\n");
fun captureTypes label th = (print(label ^ "="); app (fn v =>
 print(term_to_string v ^ ":" ^ type_to_string(type_of v) ^ ";"))
 (fst(strip_forall(concl th)) @ free_vars(concl th)); print "\n");
val _ = capture "word_loc_val_def" word_loc_val_def;
val _ = captureTypes "word_loc_val_def_types" word_loc_val_def;
val _ = show_types := false;
fun observe label q = (print(label ^ "="); print_term(rconc((SIMP_CONV (srw_ss()) [] THENC EVAL THENC SIMP_CONV (srw_ss()) [] THENC EVAL) q)); print "\n");
val labs = ``insert 1 (insert 5 20 LN) LN : num num_map num_map``;
val _ = observe "word_unchanged" ``word_loc_val (100w:word8) ^labs (Word 255w) = SOME 255w``;
val _ = observe "location_hit" ``word_loc_val (100w:word8) ^labs (Loc 1 5) = SOME 120w``;
val _ = observe "location_wrap" ``word_loc_val (250w:word8) ^labs (Loc 1 5) = SOME 14w``;
val _ = observe "outer_missing" ``word_loc_val (100w:word8) ^labs (Loc 2 5) = NONE``;
val _ = observe "inner_missing" ``word_loc_val (100w:word8) ^labs (Loc 1 6) = NONE``;
val _ = observe "one_bit" ``word_loc_val (1w:1 word) ^labs (Loc 1 5) = SOME 1w``;
