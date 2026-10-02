(* Replays original theorem proof bodies with recreated local helpers.
   Exported evaluate_def/evaluate_ind are post-allow_rebind; state equality
   theorem lookup uses DB.fetch because this probe opens no theory. *)
load "preamble";
load "stackSemTheory";
open bossLib HolKernel Parse preamble stackSemTheory wordsTheory;
val _ = Globals.linewidth := 20000;
val gc_clock = GEN_ALL (prove(``   !s1 s2. (gc s1 = SOME s2) ==> s2.clock <= s1.clock``,
  fs [gc_def,LET_DEF] \\ SRW_TAC [] []
  \\ every_case_tac >> fs[]
  \\ SRW_TAC [] [] \\ fs []));
val _ = print("gc_clock_statement=" ^ term_to_string(concl gc_clock) ^ "\n");
val _ = print("gc_clock_proved=" ^ term_to_string(rhs(concl(EQT_INTRO gc_clock))) ^ "\n");
val alloc_clock = GEN_ALL (prove(``   !xs s1 vs s2. (alloc x s1 = (vs,s2)) ==> s2.clock <= s1.clock``,
  SIMP_TAC std_ss [alloc_def] \\ REPEAT STRIP_TAC
  \\ every_case_tac \\ SRW_TAC [] [] \\ fs []
  \\ Q.ABBREV_TAC `s3 = set_store AllocSize (Word x) s1`
  \\ `s3.clock=s1.clock` by (Q.UNABBREV_TAC`s3`>>fs[set_store_def])
  \\ IMP_RES_TAC gc_clock \\ fs []
  \\ UNABBREV_ALL_TAC \\ fs []
  \\ Cases_on `x'` \\ fs [] \\ SRW_TAC [] []
  \\ EVAL_TAC \\ decide_tac));
val _ = print("alloc_clock_statement=" ^ term_to_string(concl alloc_clock) ^ "\n");
val _ = print("alloc_clock_proved=" ^ term_to_string(rhs(concl(EQT_INTRO alloc_clock))) ^ "\n");
val store_const_sem_clock = GEN_ALL (prove(``  ∀s1 v s2. (store_const_sem t1 t2 s1 = (v,s2)) ==> s2.clock <= s1.clock``,
  rw [store_const_sem_def,AllCaseEqs(),unset_var_def] \\ fs [set_var_def]));
val _ = print("store_const_sem_clock_statement=" ^ term_to_string(concl store_const_sem_clock) ^ "\n");
val _ = print("store_const_sem_clock_proved=" ^ term_to_string(rhs(concl(EQT_INTRO store_const_sem_clock))) ^ "\n");
val inst_clock = GEN_ALL (prove(``  inst i s = SOME s2 ==> s2.clock <= s.clock``,
  Cases_on `i` \\ fs [inst_def,assign_def] \\ every_case_tac
  \\ SRW_TAC [] [set_var_def] \\ fs []
  \\ fs [mem_store_def] \\ SRW_TAC [] []\\
  EVAL_TAC \\ fs[]));
val _ = print("inst_clock_statement=" ^ term_to_string(concl inst_clock) ^ "\n");
val _ = print("inst_clock_proved=" ^ term_to_string(rhs(concl(EQT_INTRO inst_clock))) ^ "\n");
val sh_mem_op_clock = GEN_ALL (prove(``  sh_mem_op op r a s = (res, s') ⇒ s'. clock ≤ s.clock``,
  strip_tac>>Cases_on ‘op’>>
  fs[sh_mem_op_def,sh_mem_store_def,sh_mem_load_def,sh_mem_store32_def,
     sh_mem_load32_def,sh_mem_load16_def,sh_mem_store16_def,
     sh_mem_store_byte_def,sh_mem_load_byte_def,ffiTheory.call_FFI_def]>>
  every_case_tac>>gvs[]));
val _ = print("sh_mem_op_clock_statement=" ^ term_to_string(concl sh_mem_op_clock) ^ "\n");
val _ = print("sh_mem_op_clock_proved=" ^ term_to_string(rhs(concl(EQT_INTRO sh_mem_op_clock))) ^ "\n");
val fix_clock_IMP = GEN_ALL (prove(``fix_clock s x = (res,s1) ==> s1.clock <= s.clock``,
  Cases_on `x` \\ fs [fix_clock_def] \\ rw [] \\ fs []));
val evaluate_clock = GEN_ALL (prove(``!xs s1 vs s2. (evaluate (xs,s1) = (vs,s2)) ==> s2.clock <= s1.clock``,
  recInduct evaluate_ind \\ REPEAT STRIP_TAC
  \\ POP_ASSUM MP_TAC \\ ONCE_REWRITE_TAC [evaluate_def]
  \\ FULL_SIMP_TAC std_ss [STOP_def]
  \\ TRY BasicProvers.TOP_CASE_TAC \\ fs []
  \\ rpt (every_case_tac \\ fs []
    \\ REPEAT STRIP_TAC \\ SRW_TAC [] [empty_env_def]
    \\ IMP_RES_TAC inst_clock
    \\ IMP_RES_TAC alloc_clock
    \\ IMP_RES_TAC store_const_sem_clock
    \\ IMP_RES_TAC sh_mem_op_clock
    \\ fs [set_var_def,set_store_def,dec_clock_def,LET_THM]
    \\ rpt (pairarg_tac \\ fs [])
    \\ every_case_tac \\ fs []
    \\ imp_res_tac fix_clock_IMP \\ fs []
    \\ imp_res_tac LESS_EQ_TRANS \\ fs [] \\ rfs []
    \\ TRY decide_tac)));
val _ = print("evaluate_clock_statement=" ^ term_to_string(concl evaluate_clock) ^ "\n");
val _ = print("evaluate_clock_proved=" ^ term_to_string(rhs(concl(EQT_INTRO evaluate_clock))) ^ "\n");
val fix_clock_evaluate = GEN_ALL (prove(``fix_clock s (evaluate (xs,s)) = evaluate (xs,s)``,
  Cases_on `evaluate (xs,s)` \\ fs [fix_clock_def]
  \\ imp_res_tac evaluate_clock
  \\ fs [MIN_DEF,GSYM NOT_LESS,DB.fetch "stackSem" "state_component_equality"]));
val _ = print("fix_clock_evaluate_statement=" ^ term_to_string(concl fix_clock_evaluate) ^ "\n");
val _ = print("fix_clock_evaluate_proved=" ^ term_to_string(rhs(concl(EQT_INTRO fix_clock_evaluate))) ^ "\n");
