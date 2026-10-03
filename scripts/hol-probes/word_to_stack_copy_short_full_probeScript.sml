load "preamble"; load "helperLib"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble BasicProvers helperLib word_to_stackProofTheory word_to_stackTheory wordSemTheory stackSemTheory;
val _ = Globals.linewidth := 1000000;
val short_replay = GEN_ALL(prove(``const_addresses a words dm ∧ good_dimindex (:α) ∧
   LENGTH words < dimindex (:α) ⇒
   copy_words (LENGTH xs) a off (xs ++ chunk_to_bitmap words ++ ys) dm m =
     if LENGTH words = dimindex (:α) - 1 then
       copy_words (LENGTH xs + (LENGTH words + 1))
             (a + bytes_in_word * n2w (LENGTH words)) off
             (xs ++ chunk_to_bitmap words ++ ys) dm
             (const_writes a off words m)
     else
       SOME (a + bytes_in_word * n2w (LENGTH words),
             const_writes (a:'a word) off words m)``,
fs [chunk_to_bitmap_def]
  \\ simp [Once copy_words_def]
  \\ simp_tac std_ss [GSYM APPEND_ASSOC,EL_LENGTH_APPEND,NULL]
  \\ fs [EL_LENGTH_APPEND,NULL]
  \\ strip_tac
  \\ old_drule copy_words_for_pattern_thm
  \\ disch_then (qspec_then ‘xs ++ [chunk_to_bits words]’ mp_tac)
  \\ disch_then (assume_tac o SPEC_ALL)
  \\ fs [] \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND] \\ fs []
  \\ fs [word_msb_chunk_to_bits]));
val _ = (print "short_full="; print_thm short_replay; print "\n");
val _ = print("short_hypotheses=" ^ Int.toString(length(hyp short_replay)) ^ "\n");
val _ = print("short_proved=" ^ term_to_string(rhs(concl(EQT_INTRO short_replay))) ^ "\n");
