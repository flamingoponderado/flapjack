load "preamble"; load "stack_rawcallProofTheory";
open HolKernel Parse bossLib preamble stack_rawcallProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = (print "inst_simulation_statement="; print_term(concl evaluate_comp_Inst));
val _ = print("inst_simulation_hypotheses=" ^ Int.toString(length(hyp evaluate_comp_Inst)) ^ "\n");
