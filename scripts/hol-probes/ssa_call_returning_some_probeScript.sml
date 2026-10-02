load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory wordLangTheory;
val _ = Globals.linewidth := 1000;
val returning_some_case = Q.SPEC `Call (SOME (returns,(firstNames,secondNames),body,l1,l2)) dest args (SOME (exceptionVar,handlerBody,handlerL1,handlerL2))` ssa_cc_trans_correct;
val _ = print "returning_some_case_full=";
val _ = print_thm returning_some_case;
val _ = print "\n";
