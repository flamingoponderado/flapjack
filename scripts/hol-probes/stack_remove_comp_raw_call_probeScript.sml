load "preamble";
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble stack_removeProofTheory stackSemTheory stack_removeTheory stackPropsTheory;
val _ = Globals.linewidth := 20000;
val find_code_lemma = prove(``state_rel jump off k s t1 /\
    (case dest of INL v2 => T | INR i => i < k) /\
    find_code dest s.regs s.code = SOME x ==>
    find_code dest t1.regs t1.code = SOME (comp jump off k x) /\ reg_bound x k``,
  CASE_TAC \\ full_simp_tac(srw_ss())[find_code_def,state_rel_def,code_rel_def]
  \\ strip_tac \\ res_tac
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[] \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[] \\ res_tac);
val state_rel_IMP = prove(``state_rel jump off k s t1 ==>
    state_rel jump off k (dec_clock s) (dec_clock t1)``,
  srw_tac[][] \\ full_simp_tac(srw_ss())[state_rel_def,dec_clock_def,empty_env_def] \\ rev_full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][] \\ res_tac \\ full_simp_tac(srw_ss())[]);
val cc_raw_call = prove(``!d s. (!frame body. lookup d s.code = SOME (Seq frame body) /\ s.clock <> 0 ==> (!r s2 t1 k off jump. evaluate (body,(dec_clock s)) = (r,s2) /\ r <> SOME Error /\
     state_rel jump off k (dec_clock s) t1 /\ reg_bound body k ==>
     ?ck t2. evaluate (comp jump off k body,t1 with clock := ck + t1.clock) = (r,t2) /\
             (case r of
              | SOME (Halt _) => t2.ffi = s2.ffi
              | SOME TimeOut => t2.ffi = s2.ffi
              | SOME (FinalFFI _) => t2.ffi = s2.ffi
              | _ =>  (state_rel jump off k s2 t2)))) ==> (!r s2 t1 k off jump. evaluate ((RawCall d),s) = (r,s2) /\ r <> SOME Error /\
     state_rel jump off k s t1 /\ reg_bound (RawCall d) k ==>
     ?ck t2. evaluate (comp jump off k (RawCall d),t1 with clock := ck + t1.clock) = (r,t2) /\
             (case r of
              | SOME (Halt _) => t2.ffi = s2.ffi
              | SOME TimeOut => t2.ffi = s2.ffi
              | SOME (FinalFFI _) => t2.ffi = s2.ffi
              | _ =>  (state_rel jump off k s2 t2)))``,
 rpt strip_tac >>
simp [Once comp_def]
    \\ fs [evaluate_def,CaseEq"option",PULL_EXISTS]
    \\ old_drule (GEN_ALL (find_code_lemma |> Q.INST [`dest`|->`INL d`]))
    \\ fs [find_code_def]
    \\ disch_then old_drule \\ strip_tac \\ fs []
    \\ Cases_on `prog` \\ fs [dest_Seq_def] \\ rveq \\ fs []
    \\ once_rewrite_tac [comp_def] \\ fs [dest_Seq_def]
    \\ `t1.clock = s.clock` by fs [state_rel_def]
    \\ fs [CaseEq"bool",pair_case_eq,CaseEq"option"] \\ rveq \\ fs []
    THEN1 (qexists_tac `0` \\ fs [] \\ fs [state_rel_def])
    \\ `state_rel jump off k (dec_clock s) (dec_clock t1)` by
          (fs [state_rel_def,dec_clock_def] \\ metis_tac [])
    \\ first_x_assum old_drule \\ fs [dec_clock_def]
    \\ disch_then match_mp_tac
    \\ pop_assum kall_tac
    \\ fs [state_rel_def]
    \\ res_tac \\ fs [reg_bound_def]);
val _ = print("cc_raw_call_statement=" ^ term_to_string(concl cc_raw_call) ^ "\n");
val _ = print("cc_raw_call_proved=" ^ term_to_string(rhs(concl(EQT_INTRO cc_raw_call))) ^ "\n");
