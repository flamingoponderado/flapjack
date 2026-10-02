load "preamble";
load "lab_to_targetProofTheory";
open HolKernel Parse preamble lab_to_targetProofTheory;
val _ = Globals.max_print_depth := 1000;
val _ = Parse.temp_remove_user_printer ("num.numeral_computations", mk_var("n", numSyntax.num));
fun emit label th = if null(hyp th) then
 (print(label ^ "="); print_term(concl th); print "\n")
 else raise Fail(label ^ " has hypotheses");
val _ = emit "word_loc_byte_full_definition" word_loc_val_byte_def;
val _ = show_types := true;
val _ = emit "word_loc_byte_full_definition_types" word_loc_val_byte_def;
val _ = show_types := false;
val _ = emit "word_loc_byte_word32_le" (EVAL ``word_loc_val_byte (0w:word32) LN (\a. Word (0x44332211w:word32)) 1w F``);
val _ = emit "word_loc_byte_word32_aligned_read" (EVAL ``word_loc_val_byte (0w:word32) LN (\a. if a = 0w then Word (0x44332211w:word32) else Loc 7 3) 1w F``);
val _ = emit "word_loc_byte_word32_be" (EVAL ``word_loc_val_byte (0w:word32) LN (\a. Word (0x44332211w:word32)) 1w T``);
val _ = emit "word_loc_byte_loc32_hit" (EVAL ``word_loc_val_byte (0x100w:word32) (insert 7 (insert 3 291 LN) LN) (\a. Loc 7 3) 0w F``);
val _ = emit "word_loc_byte_loc32_outer_miss" (EVAL ``word_loc_val_byte (0w:word32) LN (\a. Loc 7 3) 0w F``);
val _ = emit "word_loc_byte_loc32_inner_miss" (EVAL ``word_loc_val_byte (0w:word32) (insert 7 LN LN) (\a. Loc 7 3) 0w F``);
val _ = emit "word_loc_byte_word1_le" (CONV_RULE (RAND_CONV (SIMP_CONV std_ss [arithmeticTheory.MOD_0] THENC EVAL)) (EVAL ``word_loc_val_byte (0w:word1) LN (\a. Word (1w:word1)) 1w F``));
val _ = emit "word_loc_byte_word1_be" (EVAL ``word_loc_val_byte (0w:word1) LN (\a. Word (1w:word1)) 1w T``);
val _ = emit "word_loc_byte_word1_symbolic_alignment" (EVAL ``word_loc_val_byte (0w:word1) LN (\a. Word a) 1w T``);
val _ = OS.Process.exit OS.Process.success;
