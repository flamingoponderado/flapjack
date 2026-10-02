load "preamble"; load "stack_rawcallProofTheory";
open HolKernel Parse bossLib preamble stack_rawcallProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = (print "if_full_statement="; print_term(concl comp_correct));
val _ = print("if_full_hypotheses=" ^ Int.toString(length(hyp comp_correct)) ^ "\n");
val _ = (print "if_case_statement="; print_term(concl(ISPEC ``stackLang$If comparison register operand branchOne branchTwo:64 stackLang$prog`` comp_correct)));
