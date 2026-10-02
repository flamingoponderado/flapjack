load "preamble";
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble stack_removeProofTheory stackSemTheory stack_removeTheory stackPropsTheory;
val _ = Globals.linewidth := 20000;
val state_rel_get_var = prove(``state_rel jump off k s t /\ n < k ==> (get_var n s = get_var n t)``,
  full_simp_tac(srw_ss())[state_rel_def,get_var_def]);
val state_rel_IMP = prove(``state_rel jump off k s t1 ==>
    state_rel jump off k (dec_clock s) (dec_clock t1)``,
  srw_tac[][] \\ full_simp_tac(srw_ss())[state_rel_def,dec_clock_def,empty_env_def] \\ rev_full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][] \\ res_tac \\ full_simp_tac(srw_ss())[]);
val cc_jump_lower = prove(``!r1 r2 dest s. (!left right prog. get_var r1 s = SOME (Word left) /\ get_var r2 s = SOME (Word right) /\ word_cmp Lower left right /\ lookup dest s.code = SOME prog /\ s.clock <> 0 ==> (!r s2 t1 k off jump. evaluate (prog,(dec_clock s)) = (r,s2) /\ r <> SOME Error /\
     state_rel jump off k (dec_clock s) t1 /\ reg_bound prog k ==>
     ?ck t2. evaluate (comp jump off k prog,t1 with clock := ck + t1.clock) = (r,t2) /\
             (case r of
              | SOME (Halt _) => t2.ffi = s2.ffi
              | SOME TimeOut => t2.ffi = s2.ffi
              | SOME (FinalFFI _) => t2.ffi = s2.ffi
              | _ =>  (state_rel jump off k s2 t2)))) ==> (!r s2 t1 k off jump. evaluate ((JumpLower r1 r2 dest),s) = (r,s2) /\ r <> SOME Error /\
     state_rel jump off k s t1 /\ reg_bound (JumpLower r1 r2 dest) k ==>
     ?ck t2. evaluate (comp jump off k (JumpLower r1 r2 dest),t1 with clock := ck + t1.clock) = (r,t2) /\
             (case r of
              | SOME (Halt _) => t2.ffi = s2.ffi
              | SOME TimeOut => t2.ffi = s2.ffi
              | SOME (FinalFFI _) => t2.ffi = s2.ffi
              | _ =>  (state_rel jump off k s2 t2)))``,
 rpt strip_tac >>
simp [Once comp_def]
    \\ full_simp_tac(srw_ss())[reg_bound_def,evaluate_def]
    \\ imp_res_tac state_rel_get_var \\ full_simp_tac(srw_ss())[find_code_def]
    \\ Cases_on `get_var r1 t1` \\ full_simp_tac(srw_ss())[] \\ Cases_on `x` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `get_var r2 t1` \\ full_simp_tac(srw_ss())[] \\ Cases_on `x` \\ full_simp_tac(srw_ss())[]
    \\ reverse (Cases_on `word_cmp Lower c c'`) \\ full_simp_tac(srw_ss())[] THEN1 (
      srw_tac[][] \\ qexists_tac`0`\\simp[])
    \\ Cases_on `lookup dest s.code` \\ full_simp_tac(srw_ss())[]
    \\ `lookup dest t1.code = SOME (comp jump off k x) /\
        reg_bound x k /\ s.clock = t1.clock` by
     (qpat_x_assum `bb ==> bbb` (K all_tac)
      \\ full_simp_tac(srw_ss())[state_rel_def,code_rel_def] \\ res_tac \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[])
    \\ full_simp_tac(srw_ss())[] \\ Cases_on `t1.clock = 0` \\ full_simp_tac(srw_ss())[]
    THEN1 (srw_tac[][] \\ qexists_tac`t1.clock` \\ full_simp_tac(srw_ss())[state_rel_def,code_rel_def])
    \\ split_pair_case_tac \\ gvs[CaseEq"bool"]
    \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
    \\ `state_rel jump off k (dec_clock s) (dec_clock t1)` by metis_tac [state_rel_IMP]
    \\ res_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    \\ qexists_tac`ck`
    \\ fsrw_tac[ARITH_ss][get_var_def,dec_clock_def]
    \\ rev_full_simp_tac(srw_ss()++ARITH_ss)[]);
val _ = print("cc_jump_lower_statement=" ^ term_to_string(concl cc_jump_lower) ^ "\n");
val _ = print("cc_jump_lower_proved=" ^ term_to_string(rhs(concl(EQT_INTRO cc_jump_lower))) ^ "\n");
