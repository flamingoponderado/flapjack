load "preamble"; load "stack_removeProofTheory";
open HolKernel Parse bossLib preamble stack_removeProofTheory;
val _ = Globals.linewidth := 1000000;

(* stack_removeProofScript.sml:3893-3902 and 4088-4098, exported originals. *)
val _ = (print "evaluate_init_code_ffi_statement="; print_term (concl (GEN_ALL evaluate_init_code_ffi)); print "\n");
val _ = print ("evaluate_init_code_ffi_hypotheses=" ^ Int.toString (length (hyp evaluate_init_code_ffi)) ^ "\n");
val _ = (print "make_init_any_ffi_statement="; print_term (concl (GEN_ALL make_init_any_ffi)); print "\n");
val _ = print ("make_init_any_ffi_hypotheses=" ^ Int.toString (length (hyp make_init_any_ffi)) ^ "\n");
