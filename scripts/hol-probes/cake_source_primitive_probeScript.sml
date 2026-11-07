load "semanticPrimitivesTheory";
load "wordsLib";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
val _ = (print "check_type="; print_type (type_of ``semanticPrimitives$check_type``); print "\n");
val _ = (print "shift8_type="; print_type (type_of ``semanticPrimitives$shift8_lookup``); print "\n");
val _ = (print "shift64_type="; print_type (type_of ``semanticPrimitives$shift64_lookup``); print "\n");
val bool_ok = rhs (concl (EVAL ``semanticPrimitives$check_type BoolT (semanticPrimitives$Boolv T)``));
val _ = (print "bool_ok="; print_term bool_ok; print "\n");
val bool_bad = rhs (concl (EVAL ``semanticPrimitives$check_type BoolT (Litv (IntLit 1))``));
val _ = (print "bool_bad="; print_term bool_bad; print "\n");
val word_ok = rhs (concl (EQT_INTRO (prove
  (``semanticPrimitives$check_type (WordT W8) (Litv (Word8 (3w:word8)))``,
   simp[semanticPrimitivesTheory.check_type_def]))));
val _ = (print "word_ok="; print_term word_ok; print "\n");
val word_bad = rhs (concl ((EVAL THENC SIMP_CONV (srw_ss()) []) ``semanticPrimitives$check_type (WordT W64) (Litv (Word8 (3w:word8)))``));
val _ = (print "word_bad="; print_term word_bad; print "\n");
val lsl8 = rhs (concl ((EVAL THENC DEPTH_CONV (CHANGED_CONV wordsLib.WORD_EVAL_CONV) THENC EVAL)
  ``semanticPrimitives$shift8_lookup Lsl (129w:word8) 8``));
val _ = (print "lsl8="; print_term lsl8; print "\n");
val lsr8 = rhs (concl ((EVAL THENC DEPTH_CONV (CHANGED_CONV wordsLib.WORD_EVAL_CONV) THENC EVAL)
  ``semanticPrimitives$shift8_lookup Lsr (129w:word8) 9``));
val _ = (print "lsr8="; print_term lsr8; print "\n");
val asr8 = rhs (concl ((EVAL THENC DEPTH_CONV (CHANGED_CONV wordsLib.WORD_EVAL_CONV) THENC EVAL)
  ``semanticPrimitives$shift8_lookup Asr (129w:word8) 9``));
val _ = (print "asr8="; print_term asr8; print "\n");
val ror8 = rhs (concl ((EVAL THENC DEPTH_CONV (CHANGED_CONV wordsLib.WORD_EVAL_CONV) THENC EVAL)
  ``semanticPrimitives$shift8_lookup Ror (129w:word8) 9``));
val _ = (print "ror8="; print_term ror8; print "\n");
val asr64 = rhs (concl ((EVAL THENC DEPTH_CONV (CHANGED_CONV wordsLib.WORD_EVAL_CONV) THENC EVAL)
  ``semanticPrimitives$shift64_lookup Asr (9223372036854775808w:word64) 65``));
val _ = (print "asr64="; print_term asr64; print "\n");
val ror64 = rhs (concl ((EVAL THENC DEPTH_CONV (CHANGED_CONV wordsLib.WORD_EVAL_CONV) THENC EVAL)
  ``semanticPrimitives$shift64_lookup Ror (9223372036854775808w:word64) 65``));
val _ = (print "ror64="; print_term ror64; print "\n");
