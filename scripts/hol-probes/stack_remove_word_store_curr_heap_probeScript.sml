load "preamble";
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble stack_removeProofTheory stackSemTheory stack_removeTheory;
val _ = Globals.linewidth := 20000;
val wc = prove(``!base s x.
  word_store base (s.store |+ (CurrHeap,x)) = word_store base s.store``,
  rpt gen_tac >> simp [word_store_def,store_list_def,FLOOKUP_UPDATE]);
val _ = print("wc_statement=" ^ term_to_string(concl wc) ^ "\n");
val _ = print("wc_types=" ^ String.concatWith ";" (map (fn v => fst(dest_var v) ^ type_to_string(type_of v)) (fst(strip_forall(concl wc)))) ^ "\n");
val _ = print("wc_proved=" ^ term_to_string(rhs(concl(EQT_INTRO wc))) ^ "\n");
