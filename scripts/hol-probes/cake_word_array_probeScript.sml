load "data_to_wordTheory"; load "wordsLib";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun capture label tm =
 let val result = EVAL tm |> CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss())
   [wordsTheory.dimindex_64, wordsTheory.dimword_def]
   THENC EVAL THENC DEPTH_CONV (CHANGED_CONV wordsLib.WORD_EVAL_CONV)))
 in print (label ^ "="); print_term (rhs (concl result)); print "\n" end;
val _ = capture "word64" ``
 let c = (ARB:data_to_word$config) with <|tag_bits := 1; len_bits := 2; pad_bits := 3; len_size := 16|> in
 data_to_word$comp c 5 2 (dataLang$Assign 3 (closLang$WordOp (closLang$WordOpw W64 Add)) [1;2] NONE) : 64 wordLang$prog # num``;
val _ = capture "array" ``
 let c = (ARB:data_to_word$config) with <|tag_bits := 1; len_bits := 2; pad_bits := 3; len_size := 16|> in
 data_to_word$comp c 5 2 (dataLang$Assign 3 (closLang$MemOp closLang$BoundsCheckArray) [1;2] NONE) : 64 wordLang$prog # num``;
val _ = capture "shift64" ``
 let c = (ARB:data_to_word$config) with <|tag_bits := 1; len_bits := 2; pad_bits := 3; len_size := 16|> in
 data_to_word$comp c 5 2 (dataLang$Assign 3 (closLang$WordOp (closLang$WordShift W64 Lsl 5)) [1] NONE) : 64 wordLang$prog # num``;
val _ = capture "shift64_large" ``
 let c = (ARB:data_to_word$config) with <|tag_bits := 1; len_bits := 2; pad_bits := 3; len_size := 16|> in
 data_to_word$comp c 5 2 (dataLang$Assign 3 (closLang$WordOp (closLang$WordShift W64 Ror 65)) [1] NONE) : 64 wordLang$prog # num``;
val _ = capture "shift64_asr_large" ``
 let c = (ARB:data_to_word$config) with <|tag_bits := 1; len_bits := 2; pad_bits := 3; len_size := 16|> in
 data_to_word$comp c 5 2 (dataLang$Assign 3 (closLang$WordOp (closLang$WordShift W64 Asr 65)) [1] NONE) : 64 wordLang$prog # num``;
val _ = capture "boundsblock" ``
 let c = (ARB:data_to_word$config) with <|tag_bits := 1; len_bits := 2; pad_bits := 3; len_size := 16|> in
 data_to_word$comp c 5 2 (dataLang$Assign 3 (closLang$BlockOp closLang$BoundsCheckBlock) [1;2] NONE) : 64 wordLang$prog # num``;
val _ = capture "wordfrom" ``
 let c = (ARB:data_to_word$config) with <|tag_bits := 1; len_bits := 2; pad_bits := 3; len_size := 16|> in
 data_to_word$comp c 5 2 (dataLang$Assign 3 (closLang$WordOp closLang$WordFromInt) [1] NONE) : 64 wordLang$prog # num``;
val _ = capture "wordto" ``
 let c = (ARB:data_to_word$config) with <|tag_bits := 1; len_bits := 2; pad_bits := 3; len_size := 16|> in
 data_to_word$comp c 5 2 (dataLang$Assign 3 (closLang$WordOp closLang$WordToInt) [1] NONE) : 64 wordLang$prog # num``;
val _ = capture "stringcmp" ``
 let c = (ARB:data_to_word$config) with <|tag_bits := 1; len_bits := 2; pad_bits := 3; len_size := 16|> in
 data_to_word$comp c 5 2 (dataLang$Assign 3 (closLang$MemOp (closLang$StringCmp F Lt)) [1;2] NONE) : 64 wordLang$prog # num``;
val _ = capture "stringcmp_fast" ``
 let c = (ARB:data_to_word$config) with <|tag_bits := 1; len_bits := 2; pad_bits := 3; len_size := 16|> in
 data_to_word$comp c 5 2 (dataLang$Assign 3 (closLang$MemOp (closLang$StringCmp T Geq)) [1;2] NONE) : 64 wordLang$prog # num``;
val _ = capture "fp_cmp_no_hardware" ``
 let c = (ARB:data_to_word$config) with <|has_fp_ops := F; has_fp_tern := F|> in
 data_to_word$comp c 5 2 (dataLang$Assign 3 (closLang$WordOp (closLang$FP_cmp FP_Less)) [1;2] NONE) : 64 wordLang$prog # num``;
val _ = capture "fp_bop_no_hardware" ``
 let c = (ARB:data_to_word$config) with <|has_fp_ops := F; has_fp_tern := F|> in
 data_to_word$comp c 5 2 (dataLang$Assign 3 (closLang$WordOp (closLang$FP_bop FP_Add)) [1;2] NONE) : 64 wordLang$prog # num``;
val _ = capture "fp_uop_no_hardware" ``
 let c = (ARB:data_to_word$config) with <|has_fp_ops := F; has_fp_tern := F|> in
 data_to_word$comp c 5 2 (dataLang$Assign 3 (closLang$WordOp (closLang$FP_uop FP_Neg)) [1] NONE) : 64 wordLang$prog # num``;
val _ = capture "fp_top_no_hardware" ``
 let c = (ARB:data_to_word$config) with <|has_fp_ops := F; has_fp_tern := F|> in
 data_to_word$comp c 5 2 (dataLang$Assign 3 (closLang$WordOp (closLang$FP_top FP_Fma)) [1;2;3] NONE) : 64 wordLang$prog # num``;
val _ = capture "fp_top_no_ternary" ``
 let c = (ARB:data_to_word$config) with <|has_fp_ops := T; has_fp_tern := F|> in
 data_to_word$comp c 5 2 (dataLang$Assign 3 (closLang$WordOp (closLang$FP_top FP_Fma)) [1;2;3] NONE) : 64 wordLang$prog # num``;
