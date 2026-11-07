load "word_bignumTheory"; load "data_to_wordTheory"; load "wordsLib";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val entry = EVAL ``MAP (\(loc, arity, body). (loc, arity, body, 0))
  (word_bignum$generated_bignum_stubs data_to_word$Bignum_location) : (num # num # 64 wordLang$prog # num) list``;
val _ = (print "entry="; print_term (rhs (concl (CONV_RULE
  (RAND_CONV (SIMP_CONV (srw_ss()) [wordsTheory.dimindex_64, wordsTheory.dimword_def] THENC EVAL THENC DEPTH_CONV (CHANGED_CONV wordsLib.WORD_EVAL_CONV))) entry))); print "\n");
