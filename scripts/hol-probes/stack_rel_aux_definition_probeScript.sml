load "preamble"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble word_to_stackProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = (print "stack_rel_aux_definition="; print_term(concl stack_rel_aux_def));
val _ = print("stack_rel_aux_hypotheses=" ^ Int.toString(length(hyp stack_rel_aux_def)) ^ "\n");
val _ = (print "stack_rel_aux_type="; print_type(type_of ``word_to_stackProof$stack_rel_aux``); print "\n");
