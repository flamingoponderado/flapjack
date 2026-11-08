load "preamble"; load "data_to_word_memoryProofTheory";
open bossLib HolKernel Parse preamble data_to_word_memoryProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = (print "blocks_unique_thunk_typed="; Lib.with_flag (Globals.show_types,true)
  print_term (concl blocks_unique_Thunk); print "\n");
val _ = (print "blocks_unique_thunk2_typed="; Lib.with_flag (Globals.show_types,true)
  print_term (concl blocks_unique_Thunk2); print "\n");
val _ = (print "blocks_unique_word64_typed="; Lib.with_flag (Globals.show_types,true)
  print_term (concl blocks_unique_Word64); print "\n");
