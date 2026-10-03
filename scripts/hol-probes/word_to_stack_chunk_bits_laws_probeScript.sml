load "preamble"; load "helperLib"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble BasicProvers helperLib word_to_stackProofTheory word_to_stackTheory;
val _ = Globals.linewidth := 1000000;
val chunk_to_bits_bound_replay = GEN_ALL(prove(``∀ws.
    LENGTH ws < dimindex (:α) ⇒
    (chunk_to_bits ws : 'a word) ' (LENGTH ws) ∧
    ∀i. LENGTH ws < i ∧ i < dimindex (:'a) ⇒ ~(chunk_to_bits ws : 'a word) ' i``,
Induct \\ fs [chunk_to_bits_def,word_index,FORALL_PROD]
  \\ gen_tac \\ strip_tac \\ gvs []
  \\ ‘chunk_to_bits ws ≪ 1 + 1w = (chunk_to_bits ws ≪ 1) || 1w’ by
   (irule WORD_ADD_OR
    \\ fs [fcpTheory.CART_EQ,word_and_def,word_index,fcpTheory.FCP_BETA,word_lsl_def])
  \\ fs [] \\ IF_CASES_TAC \\ fs []
  \\ fs [word_or_def,fcpTheory.FCP_BETA,word_lsl_def,word_index]));
val _ = (print "chunk_to_bits_bound_full="; print_thm chunk_to_bits_bound_replay; print "\n");
val _ = print("chunk_to_bits_bound_hypotheses=" ^ Int.toString(length(hyp chunk_to_bits_bound_replay)) ^ "\n");
val _ = print("chunk_to_bits_bound_proved=" ^ term_to_string(rhs(concl(EQT_INTRO chunk_to_bits_bound_replay))) ^ "\n");
val chunk_to_bits_0_replay = GEN_ALL(prove(``chunk_to_bits ((b,w)::words) ' 0 ⇔ b``,
fs [chunk_to_bits_def]
  \\ ‘chunk_to_bits words ≪ 1 + 1w = (chunk_to_bits words ≪ 1) || 1w’ by
    (irule WORD_ADD_OR
     \\ fs [fcpTheory.CART_EQ,word_and_def,word_index,fcpTheory.FCP_BETA,word_lsl_def])
  \\ fs [] \\ rw []
  \\ fs [word_or_def,fcpTheory.FCP_BETA,word_lsl_def,word_index]));
val _ = (print "chunk_to_bits_0_full="; print_thm chunk_to_bits_0_replay; print "\n");
val _ = print("chunk_to_bits_0_hypotheses=" ^ Int.toString(length(hyp chunk_to_bits_0_replay)) ^ "\n");
val _ = print("chunk_to_bits_0_proved=" ^ term_to_string(rhs(concl(EQT_INTRO chunk_to_bits_0_replay))) ^ "\n");
