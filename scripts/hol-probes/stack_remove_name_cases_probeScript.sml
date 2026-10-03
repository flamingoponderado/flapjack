load "preamble";
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble wordsTheory stack_removeProofTheory stack_removeTheory;
val _ = Globals.linewidth := 20000;
val nc = prove(``!name. name <> CurrHeap ==> MEM name store_list``,
  Cases_on `name` \\ fs [store_list_def]
  \\ CCONTR_TAC \\ fs [] \\ Cases_on `c`
  \\ full_simp_tac std_ss [n2w_11,EVAL ``dimword (:5)``]
  \\ ntac 16 (Cases_on `n` \\ full_simp_tac std_ss [ADD1]
              \\ Cases_on `n'` \\ full_simp_tac std_ss [ADD1,GSYM ADD_ASSOC])
  \\ pop_assum mp_tac \\ rpt (pop_assum kall_tac) \\ decide_tac
);
val _ = print("nc_statement=" ^ term_to_string(concl nc) ^ "\n");
val _ = print("nc_types=" ^ String.concatWith ";" (map (fn v => fst(dest_var v) ^ type_to_string(type_of v)) (fst(strip_forall(concl nc)))) ^ "\n");
val _ = print("nc_proved=" ^ term_to_string(rhs(concl(EQT_INTRO nc))) ^ "\n");
