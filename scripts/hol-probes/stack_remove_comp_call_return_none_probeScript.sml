load "preamble";
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble stack_removeProofTheory stackSemTheory stack_removeTheory stackPropsTheory;
val _ = Globals.linewidth := 20000;
val find_code_lemma2 = prove(``state_rel jump off k s t1 /\
    (case dest of INL v2 => T | INR i => i < k) /\
    find_code dest (s.regs \\ x1) s.code = SOME x ==>
    find_code dest (t1.regs \\ x1) t1.code = SOME (comp jump off k x) /\ reg_bound x k``,
  CASE_TAC \\ full_simp_tac(srw_ss())[find_code_def,state_rel_def,code_rel_def]
  \\ strip_tac \\ res_tac
  \\ fs[DOMSUB_FLOOKUP_THM]
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[] \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[] \\ res_tac
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[] \\ res_tac);
val state_rel_with_clock = prove(``state_rel jump off k s t1 ==>
    state_rel jump off k (s with clock := c) (t1 with clock := c)``,
  srw_tac[][] \\ full_simp_tac(srw_ss())[state_rel_def,dec_clock_def,empty_env_def] \\ rev_full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][] \\ res_tac \\ full_simp_tac(srw_ss())[]);
(* Original returning prefix and handler-NONE exception proof. Specializing
   the AST option removes the handler-SOME branch and its selector combinator.
   Branch proof tactics are unchanged; full comp_correct is not assumed. *)
val cc_call_return_none = prove(``!x dest s. (!prog. find_code dest (s.regs \\ (FST (SND x))) s.code = SOME prog /\ s.clock <> 0 ==> (!r s2 t1 k off jump. evaluate (prog,dec_clock (set_var (FST (SND x)) (Loc (FST (SND (SND x))) (SND (SND (SND x)))) s)) = (r,s2) /\ r <> SOME Error /\
 state_rel jump off k (dec_clock (set_var (FST (SND x)) (Loc (FST (SND (SND x))) (SND (SND (SND x)))) s)) t1 /\ reg_bound (prog) k ==>
 ?ck t2. evaluate (comp jump off k (prog),t1 with clock := ck + t1.clock) = (r,t2) /\
 (case r of SOME (Halt _) => t2.ffi = s2.ffi | SOME TimeOut => t2.ffi = s2.ffi
 | SOME (FinalFFI _) => t2.ffi = s2.ffi | _ => state_rel jump off k s2 t2))) /\
 (!prog middle. find_code dest (s.regs \\ (FST (SND x))) s.code = SOME prog /\ s.clock <> 0 /\
 evaluate (prog,dec_clock (set_var (FST (SND x)) (Loc (FST (SND (SND x))) (SND (SND (SND x)))) s)) = (SOME (Result (Loc (FST (SND (SND x))) (SND (SND (SND x))))),middle) ==>
 (!r s2 t1 k off jump. evaluate (FST x,middle) = (r,s2) /\ r <> SOME Error /\
 state_rel jump off k (middle) t1 /\ reg_bound (FST x) k ==>
 ?ck t2. evaluate (comp jump off k (FST x),t1 with clock := ck + t1.clock) = (r,t2) /\
 (case r of SOME (Halt _) => t2.ffi = s2.ffi | SOME TimeOut => t2.ffi = s2.ffi
 | SOME (FinalFFI _) => t2.ffi = s2.ffi | _ => state_rel jump off k s2 t2))) ==> (!r s2 t1 k off jump. evaluate (Call (SOME x) dest NONE,s) = (r,s2) /\ r <> SOME Error /\
 state_rel jump off k (s) t1 /\ reg_bound (Call (SOME x) dest NONE) k ==>
 ?ck t2. evaluate (comp jump off k (Call (SOME x) dest NONE),t1 with clock := ck + t1.clock) = (r,t2) /\
 (case r of SOME (Halt _) => t2.ffi = s2.ffi | SOME TimeOut => t2.ffi = s2.ffi
 | SOME (FinalFFI _) => t2.ffi = s2.ffi | _ => state_rel jump off k s2 t2))``,
 rpt strip_tac >>
PairCases_on `x` \\ full_simp_tac(srw_ss())[reg_bound_def]
    \\ simp[Once comp_def]
    \\ qhdtm_x_assum`evaluate`mp_tac
    \\ simp[Once evaluate_def]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ old_drule (GEN_ALL find_code_lemma2)
    \\ disch_then old_drule
    \\ disch_then old_drule
    \\ strip_tac
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    >- (
      strip_tac \\ rveq
      \\ simp[evaluate_def]
      \\ qexists_tac`0`\\simp[]
      \\ `t1.clock = 0` by fs[state_rel_def]
      \\ simp[] \\ fs[state_rel_def] )
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ simp[Once evaluate_def]
    \\ `t1.clock = s.clock` by fs[state_rel_def]
    \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ qmatch_assum_rename_tac`_ = (SOME res,_)`
    \\ Cases_on`res = TimeOut` \\ fs[]
    >- (
      strip_tac \\ rveq \\ fs[]
      \\ qmatch_asmsub_abbrev_tac`state_rel _ _ _ ss _`
      \\ (fn g => subterm (fn tm => (sg `state_rel jump off k ss (^tm with clock := s.clock - 1)`) g) (#2 g))
      >- (
        simp[Abbr`ss`,dec_clock_def]
        \\ match_mp_tac state_rel_with_clock
        \\ match_mp_tac state_rel_set_var
        \\ simp[] )
      \\ first_x_assum old_drule
      \\ simp[]
      \\ strip_tac
      \\ fs[dec_clock_def]
      \\ qexists_tac`ck'`\\simp[] )
    \\ Cases_on`∃w. res = Halt w` \\ fs[]
    >- (
      strip_tac \\ rveq \\ fs[]
      \\ qmatch_asmsub_abbrev_tac`state_rel _ _ _ ss _`
      \\ (fn g => subterm (fn tm => (sg `state_rel jump off k ss (^tm with clock := s.clock - 1)`) g) (#2 g))
      >- (
        simp[Abbr`ss`,dec_clock_def]
        \\ match_mp_tac state_rel_with_clock
        \\ match_mp_tac state_rel_set_var
        \\ simp[] )
      \\ first_x_assum old_drule
      \\ simp[]
      \\ strip_tac
      \\ fs[dec_clock_def]
      \\ qexists_tac`ck'`\\simp[] )
    \\ Cases_on`∃l. res = Result l` \\ fs[]
    >- (
      BasicProvers.TOP_CASE_TAC \\ fs[]
      \\ strip_tac \\ fs[] \\ rfs[]
      \\ qmatch_asmsub_abbrev_tac`state_rel _ _ _ (dec_clock sss) _`
      \\ qabbrev_tac`ss = dec_clock sss`
      \\ (fn g => subterm (fn tm => (sg `state_rel jump off k ss (^tm with clock := s.clock - 1)`) g) (#2 g))
      >- (
        simp[Abbr`ss`,dec_clock_def,Abbr`sss`]
        \\ match_mp_tac state_rel_with_clock
        \\ match_mp_tac state_rel_set_var
        \\ simp[] )
      \\ first_x_assum old_drule \\ simp[] \\ strip_tac
      \\ first_x_assum old_drule \\ simp[] \\ strip_tac
      \\ fs[dec_clock_def]
      \\ qhdtm_x_assum`evaluate`mp_tac
      \\ qmatch_goalsub_rename_tac`ck2 + t2.clock`
      \\ old_drule (GEN_ALL evaluate_add_clock)
      \\ disch_then(qspec_then`ck2`mp_tac)
      \\ simp[] \\ ntac 2 strip_tac
      \\ qexists_tac`ck' + ck2` \\  simp[] )
    \\ Cases_on`∃f. res = FinalFFI f` \\ fs[]
    >- (
      strip_tac \\ rveq \\ fs[]
      \\ qmatch_asmsub_abbrev_tac`state_rel _ _ _ ss _`
      \\ (fn g => subterm (fn tm => (sg `state_rel jump off k ss (^tm with clock := s.clock - 1)`) g) (#2 g))
      >- (
        simp[Abbr`ss`,dec_clock_def]
        \\ match_mp_tac state_rel_with_clock
        \\ match_mp_tac state_rel_set_var
        \\ simp[] )
      \\ first_x_assum old_drule
      \\ simp[]
      \\ strip_tac
      \\ fs[dec_clock_def]
      \\ qexists_tac`ck'`\\simp[] )
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ (
      strip_tac \\ rveq
      \\ qmatch_asmsub_abbrev_tac`state_rel _ _ _ ss _`
      \\ (fn g => subterm (fn tm => (sg `state_rel jump off k ss (^tm with clock := s.clock - 1)`) g) (#2 g))
      >- (
        simp[Abbr`ss`,dec_clock_def]
        \\ match_mp_tac state_rel_with_clock
        \\ match_mp_tac state_rel_set_var
        \\ simp[] )
      \\ first_x_assum old_drule
      \\ simp[]
      \\ strip_tac
      \\ fs[dec_clock_def]
      \\ qexists_tac`ck'`\\simp[] ));
val _ = print("cc_call_return_none_statement=" ^ term_to_string(concl cc_call_return_none) ^ "\n");
val _ = print("cc_call_return_none_proved=" ^ term_to_string(rhs(concl(EQT_INTRO cc_call_return_none))) ^ "\n");
