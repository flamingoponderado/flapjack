load "preamble"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble word_to_stackProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = (print "state_rel_definition="; print_term(concl state_rel_def));
val _ = print("state_rel_hypotheses=" ^ Int.toString(length(hyp state_rel_def)) ^ "\n");
val _ = (print "state_rel_type="; print_type(type_of ``word_to_stackProof$state_rel``));
