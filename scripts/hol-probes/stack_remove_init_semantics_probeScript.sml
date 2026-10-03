load "preamble"; load "helperLib"; load "stack_removeProofTheory";
open HolKernel Parse bossLib preamble BasicProvers helperLib stack_removeProofTheory
 stack_removeTheory stackLangTheory stackSemTheory stackPropsTheory;
val _ = Globals.linewidth := 1000000;
(* The script-local overload of stack_removeProofScript.sml:17. *)
val _ = overload_on ("num_stubs", ``stack_num_stubs``);

(* Exported originals 3856-3986 and 4069-4086. *)
val _ = (print "evaluate_init_code_statement="; print_term (concl (GEN_ALL evaluate_init_code)); print "\n");
val _ = print ("evaluate_init_code_hypotheses=" ^ Int.toString (length (hyp evaluate_init_code)) ^ "\n");
val _ = (print "init_semantics_statement="; print_term (concl (GEN_ALL init_semantics)); print "\n");
val _ = print ("init_semantics_hypotheses=" ^ Int.toString (length (hyp init_semantics)) ^ "\n");
val _ = (print "make_init_opt_SOME_semantics_statement="; print_term (concl (GEN_ALL make_init_opt_SOME_semantics)); print "\n");
val _ = print ("make_init_opt_SOME_semantics_hypotheses=" ^ Int.toString (length (hyp make_init_opt_SOME_semantics)) ^ "\n");
val _ = (print "make_init_semantics_statement="; print_term (concl (GEN_ALL make_init_semantics)); print "\n");
val _ = print ("make_init_semantics_hypotheses=" ^ Int.toString (length (hyp make_init_semantics)) ^ "\n");
