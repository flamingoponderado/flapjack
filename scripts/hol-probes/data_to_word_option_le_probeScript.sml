load "preamble"; load "backendPropsTheory"; load "data_to_wordTheory"; load "wordSemTheory"; load "dataSemTheory";
open HolKernel Parse bossLib preamble backendPropsTheory data_to_wordTheory wordSemTheory dataSemTheory;
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

(* Literal replay of data_to_wordProofScript.sml:1768-1777. *)
Definition get_limits_def:
  get_limits c (t :('a, 'c, 'ffi) wordSem$state) =
    <| stack_limit := t.stack_limit
     ; heap_limit := w2n (theWord (t.store ' HeapLength)) DIV (dimindex (:'a) DIV 8)
     ; length_limit := c.len_size
     ; arch_64_bit := (dimindex (:'a) = 64)
     ; has_fp_ops := c.has_fp_ops
     ; has_fp_tops := c.has_fp_tern
     |>
End
val _ = (print "get_limits_def_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl get_limits_def); print "\n");
