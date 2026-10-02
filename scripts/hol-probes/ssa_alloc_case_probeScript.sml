load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory wordLangTheory;
val _ = Globals.linewidth := 1000;
val alloc_case = Q.SPEC `Alloc num names` ssa_cc_trans_correct;
val _ = print "alloc_case_full=";
val _ = print_thm alloc_case;
val _ = print "\n";
