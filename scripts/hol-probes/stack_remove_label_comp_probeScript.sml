load "preamble";
load "stack_removeProofTheory";
open stackLangTheory backend_commonTheory bossLib HolKernel Parse preamble stack_removeProofTheory stack_removeTheory stackSemTheory;
val _ = Globals.linewidth := 20000;
val lf = prove(``!k n. get_labels (stack_free k n) = {}``,
  recInduct stack_free_ind \\ rw []
  \\ once_rewrite_tac [stack_free_def] \\ rw []
  \\ fs [get_labels_def,single_stack_free_def]);
val la = prove(``!jump k n. get_labels (stack_alloc jump k n) = {}``,
  recInduct stack_alloc_ind \\ rw []
  \\ once_rewrite_tac [stack_alloc_def] \\ rw []
  \\ fs [get_labels_def,single_stack_alloc_def]
  \\ IF_CASES_TAC \\ fs[get_labels_def,halt_inst_def]);
val lu = prove(``!n n0. get_labels (upshift n n0) = {}``,
  recInduct upshift_ind \\ rw []
  \\ once_rewrite_tac [upshift_def] \\ rw []
  \\ fs [get_labels_def]);
val ld = prove(``!n n0. get_labels (downshift n n0) = {}``,
  recInduct downshift_ind \\ rw []
  \\ once_rewrite_tac [downshift_def] \\ rw []
  \\ fs [get_labels_def]);
val get_labels_stack_free = lf;
val get_labels_stack_alloc = la;
val get_labels_upshift = lu;
val get_labels_downshift = ld;
val get_labels_comp = prove(``!jump off k e. get_labels (comp jump off k e) = get_labels e``,
  recInduct comp_ind \\ rw [] \\ Cases_on `p`
  \\ once_rewrite_tac [comp_def] \\ fs [get_labels_def,copy_loop_def,copy_each_def] \\ rw []
  \\ fs [get_labels_def,list_Seq_def]
  \\ every_case_tac
  \\ fs [get_labels_stack_alloc,get_labels_stack_free,stack_store_def,stack_load_def,get_labels_def]
  \\ metis_tac[get_labels_upshift,get_labels_downshift]);
val _ = print("lc_statement=" ^ term_to_string(concl get_labels_comp) ^ "\n");
val _ = print("lc_proved=" ^ term_to_string(rhs(concl(EQT_INTRO get_labels_comp))) ^ "\n");
val code_rel_loc_check = prove(``code_rel jump off k c1 c2 /\ loc_check c1 (l1,l2) ==> loc_check c2 (l1,l2)``,
  fs [loc_check_def,code_rel_def,domain_lookup,PULL_EXISTS] \\ rw []
  \\ res_tac \\ fs [] \\ disj2_tac
  \\ asm_exists_tac \\ fs [get_labels_comp]);
val _ = print("ll_statement=" ^ term_to_string(concl code_rel_loc_check) ^ "\n");
val _ = print("ll_proved=" ^ term_to_string(rhs(concl(EQT_INTRO code_rel_loc_check))) ^ "\n");
