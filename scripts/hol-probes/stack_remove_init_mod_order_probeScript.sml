load "preamble";
load "stack_removeProofTheory";
open HolKernel Parse bossLib preamble stack_removeProofTheory;
val _ = Globals.linewidth := 1000000;
(* Local original declaration is replayed with its unchanged statement/proof. *)
val original = GEN_ALL(prove(``m MOD k <= n /\ m < k ==> m <= n``,rw [] >> fs []));
val _ = if null(hyp original) andalso null(free_vars(concl original)) then () else raise Fail "open theorem";
val _ = (print "init_mod_order_statement="; print_term(concl original); print "\n");
val _ = print("init_mod_order_proved=" ^ term_to_string(rhs(concl(EQT_INTRO original))) ^ "\n");
val _ = print("init_mod_order_hypotheses=" ^ Int.toString(length(hyp original)) ^ "\n");
