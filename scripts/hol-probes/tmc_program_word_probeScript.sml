load "bvi_tmcTheory"; load "bvi_inlineTheory"; load "bvi_to_dataTheory"; load "data_to_wordTheory"; load "wordsLib";
val _ = computeLib.add_funs [bvi_to_dataTheory.op_requires_names_eqn];
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val entry = EVAL ``
 let call = bvi$Call 2 (SOME 3) [bvi$Var 0] NONE in
 let code = SND (bvi_tmc$compile_prog T 59
   [(3,1,bvi$Op (closLang$BlockOp (closLang$Cons 0)) [bvi$Var 0; call]); (7,0,bvi$Var 0)]) in
 let code = SND (bvi_inline$compile_prog code) in
 let data = MAP bvi_to_data$compile_part code in
 let conf = (ARB:data_to_word$config) with <|tag_bits := 1; len_bits := 2; pad_bits := 3; len_size := 16; call_empty_ffi := F; gc_kind := data_to_word$Simple; has_div := F; has_longdiv := F|> in
 MAP (\part. let (loc, arity, body) = data_to_word$compile_part conf part in (loc, arity, body, 0)) data : (num # num # 64 wordLang$prog # num) list``;
val _ = (print "entry="; print_term (rhs (concl (CONV_RULE
  (RAND_CONV (SIMP_CONV (srw_ss()) [wordsTheory.dimindex_64, wordsTheory.dimword_def] THENC EVAL THENC DEPTH_CONV (CHANGED_CONV wordsLib.WORD_EVAL_CONV))) entry))); print "\n");
