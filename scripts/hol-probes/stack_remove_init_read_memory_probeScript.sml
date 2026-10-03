load "preamble";
load "stack_removeProofTheory";
load "helperLib";
open HolKernel Parse bossLib preamble stack_removeProofTheory stack_removeTheory miscTheory set_sepTheory helperLib;
val _ = Globals.linewidth := 20000;
val original = GEN_ALL (prove (``!xs a p. (p * word_list a xs) (fun2set (m,dm)) ==> read_mem a m (LENGTH xs) = xs``,
  Induct >> fs [read_mem_def,word_list_def,STAR_ASSOC] >> rw [] >> res_tac >> SEP_R_TAC));
val _ = print ("init_read_memory_statement=" ^ term_to_string(concl original) ^ "\n");
val _ = print ("init_read_memory_hypotheses=" ^ Int.toString(length(hyp original)) ^ "\n");
val _ = print ("init_read_memory_proved=" ^ term_to_string(rhs(concl(EQT_INTRO (GEN_ALL original)))) ^ "\n");
