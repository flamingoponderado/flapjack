load "preamble"; load "data_to_word_memoryProofTheory";
open bossLib HolKernel Parse preamble wordsTheory data_to_word_memoryProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = (print "blocks_unique_thunk_typed="; Lib.with_flag (Globals.show_types,true)
  print_term (concl blocks_unique_Thunk); print "\n");
val _ = (print "blocks_unique_thunk2_typed="; Lib.with_flag (Globals.show_types,true)
  print_term (concl blocks_unique_Thunk2); print "\n");
val _ = (print "blocks_unique_word64_typed="; Lib.with_flag (Globals.show_types,true)
  print_term (concl blocks_unique_Word64); print "\n");
val _ = (print "memory_rel_thunk_imp_typed="; Lib.with_flag (Globals.show_types,true)
  print_term (concl memory_rel_Thunk_IMP); print "\n");
(* The source theorem is local, so replay its original statement and proof. *)
val thunk_tag_bits_replay = prove (
  ``(thunk_tag_to_bits Evaluated ≪ 3 ‖ 6w) = 14w:'a word``,
  simp [thunk_tag_to_bits_def,WORD_MUL_LSL]);
val _ = (print "thunk_tag_bits_lemma_typed="; Lib.with_flag (Globals.show_types,true)
  print_term (concl thunk_tag_bits_replay); print "\n");
val _ = (print "memory_rel_thunk_inlined_typed="; Lib.with_flag (Globals.show_types,true)
  print_term (concl memory_rel_Thunk_inlined); print "\n");
