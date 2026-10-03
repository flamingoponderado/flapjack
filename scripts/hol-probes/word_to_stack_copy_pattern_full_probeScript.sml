load "preamble"; load "helperLib"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble BasicProvers helperLib word_to_stackProofTheory word_to_stackTheory wordSemTheory stackSemTheory;
val _ = Globals.linewidth := 1000000;
val pattern_replay = GEN_ALL(prove(``∀words xs a off ys dm m.
    LENGTH words < dimindex (:α) ∧ const_addresses a words dm ⇒
    copy_words_for_pattern (chunk_to_bits words) (LENGTH xs) (a:'a word) off
      (xs ++ MAP SND words ++ ys) dm m =
    SOME (LENGTH xs + LENGTH words,
          a + bytes_in_word * n2w (LENGTH words),
          const_writes a off words m)``,
Induct \\ fs [FORALL_PROD]
  THEN1 (EVAL_TAC \\ fs [])
  \\ rw [] \\ gvs [const_addresses_def]
  \\ once_rewrite_tac [copy_words_for_pattern_def]
  \\ gvs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ fs [EL_LENGTH_APPEND,chunk_to_bits_0]
  \\ ‘LENGTH ((p_1,p_2)::words) < dimindex (:α)’ by fs []
  \\ old_drule chunk_to_bits_bound \\ strip_tac \\ gvs []
  \\ conj_tac
  THEN1 (fs [fcpTheory.CART_EQ,word_index] \\ qexists_tac ‘(SUC (LENGTH words))’ \\ fs [])
  \\ IF_CASES_TAC
  THEN1
   (qsuff_tac ‘F’ \\ simp [] \\ pop_assum mp_tac \\ simp []
    \\ simp [fcpTheory.CART_EQ,word_index]
    \\ qexists_tac ‘(SUC (LENGTH words))’ \\ simp [fcpTheory.CART_EQ,word_index])
  \\ last_x_assum drule
  \\ ‘(chunk_to_bits ((p_1,p_2)::words) ⋙ 1) = chunk_to_bits words’ by
   (fs [chunk_to_bits_def]
    \\ ‘chunk_to_bits words ≪ 1 + 1w = (chunk_to_bits words ≪ 1) || 1w’ by
      (irule WORD_ADD_OR
       \\ fs [fcpTheory.CART_EQ,word_and_def,word_index,fcpTheory.FCP_BETA,word_lsl_def])
    \\ simp []
    \\ qsuff_tac ‘(chunk_to_bits words ≪ 1) ⋙ 1 = chunk_to_bits words’
    THEN1
     (rw []
      \\ fs [fcpTheory.CART_EQ,fcpTheory.FCP_BETA,word_or_def,word_lsl_def,word_lsr_def]
      \\ rw []
      \\ Cases_on ‘chunk_to_bits words ' i'’ \\ fs []
      \\ CCONTR_TAC \\ fs [] \\ gvs [word_index])
    \\ qsuff_tac ‘~word_msb (chunk_to_bits words)’
    THEN1
     (simp [word_msb_def,fcpTheory.CART_EQ,fcpTheory.FCP_BETA,
            word_or_def,word_lsl_def,word_lsr_def]
      \\ rw []
      \\ Cases_on ‘i = dimindex (:'a) - 1’
      \\ gvs [fcpTheory.FCP_BETA])
    \\ ‘LENGTH words < dimindex (:α)’ by fs []
    \\ old_drule chunk_to_bits_bound
    \\ strip_tac \\ fs [word_msb_def])
  \\ fs []
  \\ disch_then (qspecl_then [‘xs ++ [p_2]’,‘off’,‘ys’,
        ‘m⦇a ↦ Word (if p_1 then off + p_2 else p_2)⦈’] mp_tac)
  \\ fs [ADD1] \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ fs [const_writes_def]
  \\ fs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]));
val _ = (print "pattern_full="; print_thm pattern_replay; print "\n");
val _ = print("pattern_hypotheses=" ^ Int.toString(length(hyp pattern_replay)) ^ "\n");
val _ = print("pattern_proved=" ^ term_to_string(rhs(concl(EQT_INTRO pattern_replay))) ^ "\n");
