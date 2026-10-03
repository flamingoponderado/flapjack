load "preamble"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble word_to_stackProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = (print "stack_rel_definition="; print_term(concl stack_rel_def));
val _ = print("stack_rel_hypotheses=" ^ Int.toString(length(hyp stack_rel_def)) ^ "\n");
val _ = (print "stack_rel_type="; print_type(type_of ``word_to_stackProof$stack_rel``));
