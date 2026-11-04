load "data_to_wordTheory"; load "wordsLib";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = (print "comp_type="; print_type (type_of ``data_to_word$comp``); print "\n");
val entry = EVAL ``let conf = (ARB:data_to_word$config) with <|tag_bits := 1; len_bits := 2; pad_bits := 3; len_size := 16; call_empty_ffi := F; gc_kind := data_to_word$Simple|> in
 let p0 = dataLang$Seq (dataLang$Assign 3 (closLang$IntOp (closLang$Const (-7))) [] NONE) (dataLang$Return [3]) in
 let p1 = dataLang$If 1 (dataLang$Move 3 1) (dataLang$Seq dataLang$Tick (dataLang$Return [1;3])) in
 let p2 = dataLang$Assign 3 (closLang$BlockOp closLang$BoolNot) [1] NONE in
 let p3 = dataLang$Assign 3 (closLang$BlockOp (closLang$BoolTest ast$Equal)) [1;2] NONE in
 let p4 = dataLang$Assign 3 (closLang$IntOp (closLang$LessConstSmall 25)) [1] NONE in
 let p5 = dataLang$Assign 3 (closLang$BlockOp (closLang$LenEq 0)) [1] NONE in
 let p6 = dataLang$Assign 3 (closLang$BlockOp (closLang$TagLenEq 17 0)) [1] NONE in
 let p7 = dataLang$Assign 3 (closLang$BlockOp (closLang$TagLenEq 1152921504606846976 0)) [1] NONE in
 let p8 = dataLang$Assign 3 (closLang$BlockOp (closLang$Cons 17)) [] NONE in
 let p9 = dataLang$Assign 3 (closLang$Label 42) [] NONE in
 let p10 = dataLang$Assign 3 (closLang$GlobOp closLang$GlobalsPtr) [] NONE in
 let p11 = dataLang$Assign 3 (closLang$BlockOp (closLang$TagLenEq 0 1)) [1] NONE in
 let p12 = dataLang$Assign 3 (closLang$BlockOp (closLang$TagLenEq 1 3)) [1] NONE in
 let p13 = dataLang$Assign 3 (closLang$BlockOp (closLang$TagLenEq 1 65536)) [1] NONE in
 let p14 = dataLang$Assign 3 (closLang$BlockOp closLang$BoundsCheckBlock) [1;2] NONE in
 MAP (data_to_word$comp conf 5 2) [p0;p1;p2;p3;p4;p5;p6;p7;p8;p9;p10;p11;p12;p13;p14] : (64 wordLang$prog # num) list``;
val _ = (print "fragment="; print_term (rhs (concl (CONV_RULE
  (RAND_CONV (SIMP_CONV (srw_ss()) [wordsTheory.dimindex_64, wordsTheory.dimword_def] THENC EVAL THENC DEPTH_CONV (CHANGED_CONV wordsLib.WORD_EVAL_CONV))) entry))); print "\n");
