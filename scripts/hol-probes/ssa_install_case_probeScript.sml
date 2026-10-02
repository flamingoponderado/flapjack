load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory wordLangTheory;
val _ = Globals.linewidth := 1000;
val install_case = Q.SPEC `Install ptr len dptr dlen names` ssa_cc_trans_correct;
val _ = print "install_case_full=";
val _ = print_thm install_case;
val _ = print "\n";
