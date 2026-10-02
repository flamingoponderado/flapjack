load "preamble";
load "stack_removeProofTheory";
open stackPropsTheory stackLangTheory bossLib HolKernel Parse preamble wordsTheory stack_removeProofTheory stack_removeTheory stackSemTheory;
val _ = Globals.linewidth := 20000;
val rf = GEN_ALL (prove(``∀k n r s s2 t1.
   evaluate (StackFree n,s) = (r,s2) ∧ r ≠ SOME Error ∧
   state_rel jump off k s t1
   ⇒
   ∃ck t2.
     evaluate (stack_free k n,t1 with clock := ck + t1.clock) = (r,t2) ∧
     state_rel jump off k s2 t2``,
  ho_match_mp_tac stack_free_ind
  \\ srw_tac[][stackSemTheory.evaluate_def]
  \\ simp[Once stack_free_def]
  \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[]
  >- (
    srw_tac[][evaluate_def]
    \\ every_case_tac \\ full_simp_tac(srw_ss())[]
    \\ srw_tac[][] \\ full_simp_tac(srw_ss())[state_rel_def]
    \\ metis_tac[])
  \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[]
  >- (
    every_case_tac>>fs[]>>
    old_drule evaluate_single_stack_free>> rw[])
  \\ simp[evaluate_def]
  \\ old_drule (GEN_ALL evaluate_single_stack_free)
  \\ disch_then(qspec_then`max_stack_alloc`mp_tac o CONV_RULE(RESORT_FORALL_CONV(sort_vars["n"])))
  \\ simp[]>>
  qpat_assum`A=(r,s2)` mp_tac>>
  IF_CASES_TAC>>fs[]>>
  qpat_assum`A=(r,s2)` mp_tac>>
  IF_CASES_TAC>>fs[]>>
  impl_keep_tac >- EVAL_TAC>>
  strip_tac>>
  qabbrev_tac`s' = s with stack_space := max_stack_alloc + s.stack_space`>>
  `∃ck'. ∃t2'. evaluate (stack_free k (n - max_stack_alloc), t2 with clock := ck' + t2.clock) = (r,t2') ∧ state_rel jump off k s2 t2'`
  by (
    first_x_assum match_mp_tac >>
    qexists_tac`s'` >> simp[Abbr`s'`]>>rw[])
  \\ qhdtm_x_assum`evaluate`mp_tac
  \\ old_drule (GEN_ALL evaluate_add_clock)
  \\ disch_then(qspec_then`ck'`mp_tac)
  \\ rveq \\ fs[]
  \\ ntac 2 strip_tac
  \\ qexists_tac`ck+ck'`\\simp[]));
val _ = print("rf_statement=" ^ term_to_string(concl rf) ^ "\n");
val _ = print("rf_proved=" ^ term_to_string(rhs(concl(EQT_INTRO rf))) ^ "\n");
