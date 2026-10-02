load "preamble";
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble wordsTheory stack_removeProofTheory stack_removeTheory stackSemTheory stackPropsTheory stackLangTheory set_sepTheory;
val _ = temp_delsimps ["NORMEQ_CONV"];
val _ = diminish_srw_ss ["ABBREV"];
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"];
val _ = set_trace "BasicProvers.var_eq_old" 1;
val _ = Globals.linewidth := 20000;
val ra = GEN_ALL (prove(``   ∀jump k n r s s2 t1.
   evaluate (StackAlloc n,s) = (r,s2) ∧ r ≠ SOME Error ∧
   state_rel jump off k s t1
   ⇒
   ∃ck t2.
     evaluate (stack_alloc jump k n,t1 with clock := ck + t1.clock) = (r,t2) ∧
     if ∀w. r ≠ SOME (Halt w) then state_rel jump off k s2 t2 else t2.ffi = s2.ffi``,
  ho_match_mp_tac stack_alloc_ind
  \\ srw_tac[][stackSemTheory.evaluate_def]
  \\ simp[Once stack_alloc_def]
  \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[]
  >- (
    srw_tac[][evaluate_def]
    \\ every_case_tac \\ full_simp_tac(srw_ss())[]
    \\ srw_tac[][] \\ full_simp_tac(srw_ss())[state_rel_def]
    \\ metis_tac[])
  \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[]
  >- (
    old_drule evaluate_single_stack_alloc
    \\ impl_tac
    >- ( srw_tac[][] \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[state_rel_def] )
    \\ simp[]
    \\ strip_tac
    \\ asm_exists_tac
    \\ every_case_tac \\ full_simp_tac(srw_ss())[]
    \\ rveq \\ full_simp_tac(srw_ss())[])
  \\ simp[evaluate_def]
  \\ old_drule (GEN_ALL evaluate_single_stack_alloc)
  \\ disch_then(qspec_then`max_stack_alloc`mp_tac o CONV_RULE(RESORT_FORALL_CONV(sort_vars["n"])))
  \\ simp[]
  \\ `max_stack_alloc ≠ 0` by EVAL_TAC
  \\ simp[]
  \\ srw_tac[][]
  >- (
    qexists_tac`ck`\\simp[]
    \\ `s.stack_space < n` by decide_tac
    \\ full_simp_tac(srw_ss())[]
    \\ `s.use_stack` by full_simp_tac(srw_ss())[state_rel_def]
    \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] )
  \\ `s.use_stack` by full_simp_tac(srw_ss())[state_rel_def]
  \\ full_simp_tac(srw_ss())[]
  \\ qabbrev_tac`s' =
        if s.stack_space < n then empty_env (s with stack_space := s.stack_space - max_stack_alloc)
        else s with stack_space := s.stack_space - n`
  \\ `∃ck'. ∃t2'.
        evaluate (stack_alloc jump k (n - max_stack_alloc), t2 with clock := ck' + t2.clock) =
          (r,t2') ∧
        if ∀w. r ≠ SOME (Halt w) then
          state_rel jump off k s' t2'
       else t2'.ffi = s'.ffi`
  by (
    first_x_assum match_mp_tac
    \\ simp[]
    \\ ONCE_REWRITE_TAC[CONJ_COMM]
    \\ asm_exists_tac
    \\ simp[]
    \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[Abbr`s'`] )
  \\ qhdtm_x_assum`evaluate`mp_tac
  \\ old_drule (GEN_ALL evaluate_add_clock)
  \\ disch_then(qspec_then`ck'`mp_tac)
  \\ simp[] \\ ntac 2 strip_tac
  \\ qexists_tac`ck+ck'`\\simp[]
  \\ qhdtm_x_assum`COND`mp_tac
  \\ simp[Abbr`s'`]
  \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[]
  \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[]
  \\ rveq \\ simp[]));
val _ = print("ra_statement=" ^ term_to_string(concl ra) ^ "\n");
val _ = print("ra_proved=" ^ term_to_string(rhs(concl(EQT_INTRO ra))) ^ "\n");
