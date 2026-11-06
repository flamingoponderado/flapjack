load "data_to_wordTheory"; load "wordsLib";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun capture label tm =
 let val result = EVAL tm |> CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss())
   [wordsTheory.dimindex_64, wordsTheory.dimword_def]
   THENC EVAL THENC DEPTH_CONV (CHANGED_CONV wordsLib.WORD_EVAL_CONV)))
 in print (label ^ "="); print_term (rhs (concl result)); print "\n" end;
val _ = capture "lesseq" ``
 let c = (ARB:data_to_word$config) with <|tag_bits := 1; len_bits := 2; pad_bits := 3; len_size := 16|> in
 data_to_word$comp c 5 2 (dataLang$Assign 3 (closLang$IntOp closLang$LessEq) [1;2] NONE) : 64 wordLang$prog # num``;
val _ = capture "mod" ``
 let c = (ARB:data_to_word$config) with <|tag_bits := 1; len_bits := 2; pad_bits := 3; len_size := 16; has_div := T; has_longdiv := F|> in
 data_to_word$comp c 5 2 (dataLang$Assign 3 (closLang$IntOp closLang$Mod) [1;2] NONE) : 64 wordLang$prog # num``;
val _ = capture "bounds" ``
 let c = (ARB:data_to_word$config) with <|tag_bits := 1; len_bits := 2; pad_bits := 3; len_size := 16|> in
 data_to_word$comp c 5 2 (dataLang$Assign 3 (closLang$MemOp (closLang$BoundsCheckByte T)) [1;2] NONE) : 64 wordLang$prog # num``;
val _ = capture "ffi" ``
 let c = (ARB:data_to_word$config) with <|tag_bits := 1; len_bits := 2; pad_bits := 3; len_size := 16; call_empty_ffi := F|> in
 data_to_word$comp c 5 2 (dataLang$Assign 3 (closLang$FFI «write») [1;2] NONE) : 64 wordLang$prog # num``;
val _ = capture "list_append" ``
 let c = (ARB:data_to_word$config) with <|tag_bits := 1; len_bits := 2; pad_bits := 3; len_size := 16|> in
 data_to_word$comp c 5 2 (dataLang$Assign 3 (closLang$BlockOp closLang$ListAppend) [1;2] NONE) : 64 wordLang$prog # num``;
val _ = capture "list_append_arity" ``
 let c = (ARB:data_to_word$config) with <|tag_bits := 1; len_bits := 2; pad_bits := 3; len_size := 16|> in
 data_to_word$comp c 5 2 (dataLang$Assign 3 (closLang$BlockOp closLang$ListAppend) [1] NONE) : 64 wordLang$prog # num``;
val _ = capture "xor_byte" ``
 let c = (ARB:data_to_word$config) with <|tag_bits := 1; len_bits := 2; pad_bits := 3; len_size := 16|> in
 data_to_word$comp c 5 2 (dataLang$Assign 3 (closLang$MemOp closLang$XorByte) [1;2] NONE) : 64 wordLang$prog # num``;
val _ = capture "config_gc" ``
 let c = (ARB:data_to_word$config) with <|call_empty_ffi := F|> in
 data_to_word$comp c 5 2 (dataLang$Assign 3 (closLang$MemOp closLang$ConfigGC) [1;2] NONE) : 64 wordLang$prog # num``;
val _ = capture "config_gc_ffi" ``
 let c = (ARB:data_to_word$config) with <|call_empty_ffi := T|> in
 data_to_word$comp c 5 2 (dataLang$Assign 3 (closLang$MemOp closLang$ConfigGC) [1;2] NONE) : 64 wordLang$prog # num``;
val _ = capture "len_zero" ``
 let c = (ARB:data_to_word$config) with <|tag_bits := 1; len_bits := 2; pad_bits := 3; len_size := 16|> in
 data_to_word$comp c 5 2 (dataLang$Assign 3 (closLang$BlockOp (closLang$LenEq 0)) [1] NONE) : 64 wordLang$prog # num``;
val _ = capture "len_small" ``
 let c = (ARB:data_to_word$config) with <|tag_bits := 1; len_bits := 2; pad_bits := 3; len_size := 16|> in
 data_to_word$comp c 5 2 (dataLang$Assign 3 (closLang$BlockOp (closLang$LenEq 1)) [1] NONE) : 64 wordLang$prog # num``;
val _ = capture "len_header" ``
 let c = (ARB:data_to_word$config) with <|tag_bits := 1; len_bits := 2; pad_bits := 3; len_size := 16|> in
 data_to_word$comp c 5 2 (dataLang$Assign 3 (closLang$BlockOp (closLang$LenEq 3)) [1] NONE) : 64 wordLang$prog # num``;
val _ = capture "len_overflow" ``
 let c = (ARB:data_to_word$config) with <|tag_bits := 1; len_bits := 2; pad_bits := 3; len_size := 16|> in
 data_to_word$comp c 5 2 (dataLang$Assign 3 (closLang$BlockOp (closLang$LenEq 18446744073709551616)) [1] NONE) : 64 wordLang$prog # num``;
