load "preamble"; load "stack_removeProofTheory";
open HolKernel Parse bossLib preamble stack_removeProofTheory;
val _ = Globals.linewidth := 1000000;

(* stack_removeProofScript.sml:38-47, exported original theorem. *)
val _ = (print "word_list_exists_ADD_statement="; print_term (concl (GEN_ALL word_list_exists_ADD)); print "\n");
val _ = print ("word_list_exists_ADD_hypotheses=" ^ Int.toString (length (hyp word_list_exists_ADD)) ^ "\n");
