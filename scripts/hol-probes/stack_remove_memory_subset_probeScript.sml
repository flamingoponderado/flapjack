load "preamble";
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble stack_removeProofTheory set_sepTheory wordSemTheory;
val _ = Globals.linewidth := 20000;
val memory_fun2set_subset_replay = prove(``(memory m1 d1 * rest) (fun2set (m2,d2)) ==> d1 SUBSET d2``,
  fs [STAR_def,memory_def,fun2set_def] \\ fs [SPLIT_def]
  \\ rw [] \\ fs [EXTENSION,FORALL_PROD,SUBSET_DEF]
  \\ metis_tac []);
val _ = print("memory_subset_statement=" ^ term_to_string(concl memory_fun2set_subset_replay) ^ "\n");
val _ = print("memory_subset_proved=" ^ term_to_string(rhs(concl(EQT_INTRO memory_fun2set_subset_replay))) ^ "\n");
