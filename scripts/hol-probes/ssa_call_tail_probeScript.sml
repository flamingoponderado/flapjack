load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory wordLangTheory;
val _ = Globals.linewidth := 1000;
val tail_case = Q.SPEC `Call NONE dest args handler` ssa_cc_trans_correct;
val _ = print "tail_case_full=";
val _ = print_thm tail_case;
val _ = print "\n";
