load "preamble"; load "helperLib"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble BasicProvers helperLib word_to_stackProofTheory word_to_stackTheory wordSemTheory stackSemTheory;
val _ = Globals.linewidth := 1000000;
val _ = temp_delsimps ["NORMEQ_CONV"];
val _ = diminish_srw_ss ["ABBREV"];
val _ = temp_delsimps ["fromAList_def", "domain_union", "domain_insert",
  "domain_inter", "domain_map", "domain_difference", "sptree.map_def",
  "sptree.lookup_rwts", "sptree.insert_notEmpty", "misc.max3_def"];
val _ = numLib.temp_prefer_num();
val copy_replay = GEN_ALL(prove(``∀words xs ys a off dm m.
    const_addresses a words dm ∧ good_dimindex (:'a) ⇒
    copy_words (LENGTH xs) (a:'a word) off
      (xs ++ const_words_to_bitmap words (LENGTH words) ++ ys) dm m =
    SOME (a + bytes_in_word * n2w (LENGTH words), const_writes a off words m)``,
strip_tac
  \\ completeInduct_on ‘LENGTH words’
  \\ rpt strip_tac \\ gvs [PULL_FORALL]
  \\ rw [Once const_words_to_bitmap_def]
  THEN1
   (‘LENGTH words < dimindex (:α)’ by fs []
    \\ drule_all copy_words \\ fs [])
  THEN1 gvs [good_dimindex_def]
  \\ qabbrev_tac ‘h = (TAKE (dimindex (:α) − 1) words)’
  \\ qabbrev_tac ‘t = (DROP (dimindex (:α) − 1) words)’
  \\ gvs []
  \\ ‘LENGTH h < dimindex (:α)’ by fs [Abbr‘h’]
  \\ ‘const_addresses a h dm’ by
   (‘words = h ++ t’ by metis_tac [TAKE_DROP]
    \\ gvs [const_addresses_append])
  \\ drule_all copy_words
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ disch_then kall_tac
  \\ reverse IF_CASES_TAC THEN1 gvs [Abbr‘h’,LENGTH_TAKE]
  \\ first_x_assum (qspecl_then [‘t’,‘xs ++ chunk_to_bitmap h’,‘ys’,
       ‘a + bytes_in_word * n2w (LENGTH h)’,‘off’,‘dm’,
       ‘const_writes a off h m’] mp_tac)
  \\ rewrite_tac [AND_IMP_INTRO]
  \\ impl_tac THEN1
   (‘words = h ++ t’ by metis_tac [TAKE_DROP]
    \\ gvs [const_addresses_append])
  \\ strip_tac \\ gvs []
  \\ ‘LENGTH t = LENGTH words + 1 - dimindex (:α)’ by
    (unabbrev_all_tac \\ fs [])
  \\ ‘LENGTH (chunk_to_bitmap h) = dimindex (:α)’ by
    fs [chunk_to_bitmap_def]
  \\ fs []
  \\ qpat_x_assum ‘LENGTH t = _’ (assume_tac o GSYM)
  \\ ‘dimindex (:α) − 1 = LENGTH h’ by fs [Abbr‘h’] \\ fs []
  \\ ‘words = h ++ t’ by metis_tac [TAKE_DROP]
  \\ gvs [] \\ gvs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ fs [const_writes_append]));
val _ = (print "copy_full="; print_thm copy_replay; print "\n");
val _ = print("copy_hypotheses=" ^ Int.toString(length(hyp copy_replay)) ^ "\n");
val _ = print("copy_proved=" ^ term_to_string(rhs(concl(EQT_INTRO copy_replay))) ^ "\n");
