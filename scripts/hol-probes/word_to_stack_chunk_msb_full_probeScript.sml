load "preamble"; load "helperLib"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble BasicProvers helperLib word_to_stackProofTheory word_to_stackTheory;
val _ = Globals.linewidth := 1000000;
val msb_replay = GEN_ALL(prove(``LENGTH words < dimindex (:α) ∧ good_dimindex (:α) ⇒
  word_msb (chunk_to_bits words : 'a word) = (LENGTH words = dimindex (:α) − 1)``,
rw [] \\ old_drule chunk_to_bits_bound
  \\ Cases_on ‘LENGTH words = dimindex (:α) − 1’ \\ fs []
  \\ fs [word_msb_def] \\ rw []
  \\ first_x_assum irule \\ fs []));
val _ = (print "msb_full="; print_thm msb_replay; print "\n");
val _ = print("msb_hypotheses=" ^ Int.toString(length(hyp msb_replay)) ^ "\n");
val _ = print("msb_proved=" ^ term_to_string(rhs(concl(EQT_INTRO msb_replay))) ^ "\n");
