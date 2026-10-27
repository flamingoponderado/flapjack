load "data_to_wordTheory"; load "wordsLib";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val entry = EVAL ``let conf = (ARB:data_to_word$config) with has_longdiv := F in
 [(data_to_word$LongDiv1_location, 7, data_to_word$LongDiv1_code conf, 0);
  (data_to_word$LongDiv_location, 4, data_to_word$LongDiv_code conf, 0);
  (data_to_word$LongDiv1_location, 7, data_to_word$LongDiv1_code (conf with has_longdiv := T), 0);
  (data_to_word$LongDiv_location, 4, data_to_word$LongDiv_code (conf with has_longdiv := T), 0)] : (num # num # 64 wordLang$prog # num) list``;
val _ = (print "entry="; print_term (rhs (concl (CONV_RULE
  (RAND_CONV (SIMP_CONV (srw_ss()) [wordsTheory.dimindex_64, wordsTheory.dimword_def] THENC EVAL THENC DEPTH_CONV (CHANGED_CONV wordsLib.WORD_EVAL_CONV))) entry))); print "\n");
