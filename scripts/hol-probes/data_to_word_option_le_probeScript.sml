load "preamble"; load "backendPropsTheory";
open HolKernel Parse bossLib preamble backendPropsTheory;
val _ = new_theory "flapjack_data_to_word_option_le_replay";
val _ = Globals.linewidth := 1000000;
(* Literal source replay of data_to_wordProofScript 1779-1784 (data_to_wordProofTheory is not built here). *)
Theorem option_le_SOME:
  option_le x (SOME n) <=> ?m. x = SOME m /\ m <= n
Proof
  Cases_on `x` \\ fs []
QED

val _ = if null (hyp (option_le_SOME)) then () else raise Fail "hypotheses: option_le_SOME";
val _ = (print "option_le_SOME_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (option_le_SOME)); print "\n");
