load "preamble"; load "data_to_wordTheory"; load "data_to_word_memoryProofTheory";
open bossLib HolKernel Parse preamble wordsTheory miscTheory data_to_wordTheory data_to_word_memoryProofTheory;
val _ = Globals.linewidth := 1000000;

(* These declarations are local in the source script, so replay their original
   statements and tactics before printing their inferred types. *)
val local_word_test_lemma1 = prove (
  ``good_dimindex (:α) ⇒
    (0b111100w && x = n2w ((8 + 6) * 4):'a word ⇔
     ~ word_bit 2 x ∧ word_bit 3 x ∧ word_bit 4 x ∧ word_bit 5 x)``,
  simp [word_eq,word_bit_and,word_bit_n2w,good_dimindex_def]
  \\ rw [] \\ gvs [] \\ rw []
  \\ simp [METIS_PROVE [] “(∀n. (P n = Q n)) ⇔ (∀n. P n ⇒ Q n) ∧ (∀n. Q n ⇒ P n)”]
  \\ gvs [SF DNF_ss,SF CONJ_ss]);

val local_word_test_lemma2 = prove (
  ``good_dimindex (:α) ⇒
    (0b111100w && x = n2w ((0 + 6) * 4):'a word ⇔
     ~ word_bit 2 x ∧ word_bit 3 x ∧ word_bit 4 x ∧ ~ word_bit 5 x)``,
  simp [word_eq,word_bit_and,word_bit_n2w,good_dimindex_def]
  \\ rw [] \\ gvs [] \\ rw []
  \\ simp [METIS_PROVE [] “(∀n. (P n = Q n)) ⇔ (∀n. P n ⇒ Q n) ∧ (∀n. Q n ⇒ P n)”]
  \\ gvs [SF DNF_ss,SF CONJ_ss]
  \\ eq_tac \\ rw [] \\ gvs []
  \\ first_assum $ qspec_then ‘2’ assume_tac
  \\ first_assum $ qspec_then ‘3’ assume_tac
  \\ first_assum $ qspec_then ‘4’ assume_tac
  \\ first_assum $ qspec_then ‘5’ assume_tac
  \\ fs []);

val _ = (print "word_test_lemma1_typed="; Lib.with_flag (Globals.show_types,true)
  print_term (concl local_word_test_lemma1); print "\n");
val _ = (print "word_test_lemma2_typed="; Lib.with_flag (Globals.show_types,true)
  print_term (concl local_word_test_lemma2); print "\n");
val jump_exc_locals_replay = prove (
  ``wordSem$jump_exc (t with locals := l) = wordSem$jump_exc t``,
  fs [wordSemTheory.jump_exc_def]);
val _ = (print "jump_exc_locals_typed="; Lib.with_flag (Globals.show_types,true)
  print_term (concl jump_exc_locals_replay); print "\n");
val memory_rel_thunk_bits_replay = prove (
  ``memory_rel c be ts refs sp st m dm ((RefPtr bl p,Word (w :α word))::vars) ∧
    lookup p refs = SOME (Thunk ev z) ∧ good_dimindex (:α) ∧
    get_real_addr c st w = SOME a ∧ m a = Word x ∧ w ' 0 ⇒
    (¬bl ∧ ev = Evaluated ∧
     (0b111100w && x) ≠ n2w ((0 + 6) * 4) ∧
     (0b111100w && x) ≠ n2w ((8 + 6) * 4)) ∨
    (case ev of
     | NotEvaluated => 0b111100w && x = n2w ((0 + 6) * 4)
     | Evaluated => 0b111100w && x = n2w ((8 + 6) * 4))``,
  rw [] \\ drule_all memory_rel_Thunk_IMP \\ gvs [] \\ rw []
  \\ Cases_on ‘ev’ \\ gvs []
  \\ drule local_word_test_lemma1 \\ fs []
  \\ drule local_word_test_lemma2 \\ fs []);
val _ = (print "memory_rel_thunk_bits_typed="; Lib.with_flag (Globals.show_types,true)
  print_term (concl memory_rel_thunk_bits_replay); print "\n");
