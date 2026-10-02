load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory wordLangTheory;
val _ = Globals.linewidth := 1000;
val returning_none_case = Q.SPEC `Call (SOME (returns,(firstNames,secondNames),body,l1,l2)) dest args NONE` ssa_cc_trans_correct;
val _ = print "returning_none_case_full=";
val _ = print_thm returning_none_case;
val _ = print "\n";
