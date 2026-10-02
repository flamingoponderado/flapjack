load "preamble"; load "stack_rawcallProofTheory";
open HolKernel Parse bossLib preamble stack_rawcallProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = (print "loop_full_statement="; print_term(concl comp_correct));
val _ = print("loop_full_hypotheses=" ^ Int.toString(length(hyp comp_correct)) ^ "\n");
val _ = (print "loop_case_statement="; print_term(concl(ISPEC ``stackLang$Loop loopBody:64 stackLang$prog`` comp_correct)));
