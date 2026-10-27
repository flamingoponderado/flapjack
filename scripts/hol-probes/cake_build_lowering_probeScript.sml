load "data_to_wordTheory"; load "wordsLib";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun capture label tm =
 let val result = EVAL tm |> CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss())
   [wordsTheory.dimindex_64, wordsTheory.dimindex_32, wordsTheory.dimword_def]
   THENC EVAL THENC DEPTH_CONV (CHANGED_CONV wordsLib.WORD_EVAL_CONV)))
 in print (label ^ "="); print_term (rhs (concl result)); print "\n" end;
val _ = capture "parts64" ``
 let c = (ARB:data_to_word$config) with <|tag_bits := 1; len_bits := 2; pad_bits := 3; len_size := 16; be := F|> in
 data_to_word$const_parts_to_words c [closLang$Str «abc»; closLang$Con 0 []; closLang$Con 1 [0;1]; closLang$Int (~5)] : ((bool # 64 word_loc) # (bool # 64 word_loc) list) option``;
val _ = capture "parts32be" ``
 let c = (ARB:data_to_word$config) with <|tag_bits := 1; len_bits := 2; pad_bits := 3; len_size := 16; be := T|> in
 data_to_word$const_parts_to_words c [closLang$Str «abcd»; closLang$W64 0x1122334455667788w; closLang$Int 2147483648] : ((bool # 32 word_loc) # (bool # 32 word_loc) list) option``;
val _ = capture "build64" ``
 let c = (ARB:data_to_word$config) with <|tag_bits := 1; len_bits := 2; pad_bits := 3; len_size := 16; be := F|> in
 data_to_word$comp c 5 2 (dataLang$Assign 3 (closLang$BlockOp (closLang$Build [closLang$Int 1; closLang$Con 0 [0]])) [] NONE) : 64 wordLang$prog # num``;
val _ = capture "fromlist64" ``
 let c = (ARB:data_to_word$config) with <|tag_bits := 1; len_bits := 2; pad_bits := 3; len_size := 16; be := F|> in
 data_to_word$comp c 5 2 (dataLang$Assign 3 (closLang$BlockOp (closLang$FromList 2)) [1;2] NONE) : 64 wordLang$prog # num``;
val _ = capture "refbyte64" ``
 let c = (ARB:data_to_word$config) with <|tag_bits := 1; len_bits := 2; pad_bits := 3; len_size := 16; be := F|> in
 data_to_word$comp c 5 2 (dataLang$Assign 3 (closLang$MemOp (closLang$RefByte T)) [1;2] NONE) : 64 wordLang$prog # num``;
