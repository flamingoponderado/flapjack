load "preamble"; load "stack_removeProofTheory";
open HolKernel Parse bossLib preamble stack_removeProofTheory;
val _ = Globals.linewidth := 1000000;

(* stack_removeProofScript.sml:3225-3837, exported original theorem. *)
val _ = (print "init_code_thm_statement="; print_term (concl (GEN_ALL init_code_thm)); print "\n");
val _ = print ("init_code_thm_hypotheses=" ^ Int.toString (length (hyp init_code_thm)) ^ "\n");
