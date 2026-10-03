load "preamble"; load "stack_removeProofTheory";
open HolKernel Parse bossLib preamble stack_removeProofTheory;
val _ = Globals.linewidth := 1000000;

(* stack_removeProofScript.sml:2636-2725, exported original theorem. *)
val _ = (print "store_list_code_thm_statement="; print_term (concl (GEN_ALL store_list_code_thm)); print "\n");
val _ = print ("store_list_code_thm_hypotheses=" ^ Int.toString (length (hyp store_list_code_thm)) ^ "\n");
val _ = print ("store_list_code_thm_free_vars=" ^
  String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string (type_of v))
    (free_vars (concl store_list_code_thm))) ^ "\n");
