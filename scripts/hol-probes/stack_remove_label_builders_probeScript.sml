load "preamble";
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble stack_removeProofTheory stack_removeTheory stackSemTheory;
val _ = Globals.linewidth := 20000;
val lf = prove(``!k n. get_labels (stack_free k n) = {}``,
  recInduct stack_free_ind \\ rw []
  \\ once_rewrite_tac [stack_free_def] \\ rw []
  \\ fs [get_labels_def,single_stack_free_def]);
val _ = print("lf_statement=" ^ term_to_string(concl lf) ^ "\n");
val _ = print("lf_proved=" ^ term_to_string(rhs(concl(EQT_INTRO lf))) ^ "\n");
val la = prove(``!jump k n. get_labels (stack_alloc jump k n) = {}``,
  recInduct stack_alloc_ind \\ rw []
  \\ once_rewrite_tac [stack_alloc_def] \\ rw []
  \\ fs [get_labels_def,single_stack_alloc_def]
  \\ IF_CASES_TAC \\ fs[get_labels_def,halt_inst_def]);
val _ = print("la_statement=" ^ term_to_string(concl la) ^ "\n");
val _ = print("la_proved=" ^ term_to_string(rhs(concl(EQT_INTRO la))) ^ "\n");
val lu = prove(``!n n0. get_labels (upshift n n0) = {}``,
  recInduct upshift_ind \\ rw []
  \\ once_rewrite_tac [upshift_def] \\ rw []
  \\ fs [get_labels_def]);
val _ = print("lu_statement=" ^ term_to_string(concl lu) ^ "\n");
val _ = print("lu_proved=" ^ term_to_string(rhs(concl(EQT_INTRO lu))) ^ "\n");
val ld = prove(``!n n0. get_labels (downshift n n0) = {}``,
  recInduct downshift_ind \\ rw []
  \\ once_rewrite_tac [downshift_def] \\ rw []
  \\ fs [get_labels_def]);
val _ = print("ld_statement=" ^ term_to_string(concl ld) ^ "\n");
val _ = print("ld_proved=" ^ term_to_string(rhs(concl(EQT_INTRO ld))) ^ "\n");
