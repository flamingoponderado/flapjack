load "preamble"; load "word_simpProofTheory";
open HolKernel Parse bossLib preamble wordSemTheory word_simpTheory word_simpProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = show_types := true;
val _ = (print "gc_fun_sf_gc_consts_statement="; print_term(concl gc_fun_sf_gc_consts); print "\n");
val _ = (print "gc_fun_sf_gc_consts_hypotheses="; print(Int.toString(length(hyp gc_fun_sf_gc_consts))); print "\n");
