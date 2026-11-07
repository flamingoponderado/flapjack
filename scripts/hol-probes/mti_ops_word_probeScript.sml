load "data_to_wordTheory"; load "wordsLib";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val entry = EVAL ``let conf = (ARB:data_to_word$config) with <|tag_bits := 1; len_bits := 2; pad_bits := 3; len_size := 16; call_empty_ffi := F; has_div := F; has_longdiv := F|> in
 let (p0,n0) = data_to_word$comp conf 5 2 (dataLang$Assign 3 (closLang$BlockOp (closLang$TagEq 30)) [1] NONE) in
 let (p1,n1) = data_to_word$comp conf 5 2 (dataLang$Assign 3 (closLang$IntOp closLang$Mult) [1;2] NONE) in
 let (p2,n2) = data_to_word$comp conf 5 2 (dataLang$Assign 3 (closLang$IntOp closLang$Div) [1;2] NONE) in
 let (p3,n3) = data_to_word$comp (conf with has_div := T) 5 2 (dataLang$Assign 3 (closLang$IntOp closLang$Div) [1;2] NONE) in
 let (p4,n4) = data_to_word$comp (conf with has_longdiv := T) 5 2 (dataLang$Assign 3 (closLang$IntOp closLang$Div) [1;2] NONE) in
 let (p5,n5) = data_to_word$comp conf 5 2 (dataLang$Assign 3 (closLang$BlockOp (closLang$ConsExtend 1)) [1;2;3;4;5] NONE) in
 [(0,0,p0,n0); (1,0,p1,n1); (2,0,p2,n2); (3,0,p3,n3); (4,0,p4,n4); (5,0,p5,n5)] : (num # num # 64 wordLang$prog # num) list``;
val _ = (print "entry="; print_term (rhs (concl (CONV_RULE
  (RAND_CONV (SIMP_CONV (srw_ss()) [wordsTheory.dimindex_64, wordsTheory.dimword_def] THENC EVAL THENC DEPTH_CONV (CHANGED_CONV wordsLib.WORD_EVAL_CONV))) entry))); print "\n");
