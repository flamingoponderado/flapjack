(* Literal original Loop case body under its actual guarded induction hypotheses. *)
load "preamble";
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble stack_removeProofTheory stackSemTheory stack_removeTheory stackPropsTheory;
val _ = Globals.linewidth := 20000;
val cc_loop = prove(``!p s. (!r s2 t1 k off jump.
  evaluate (p,s) = (r,s2) /\ r <> SOME Error /\
  state_rel jump off k s t1 /\ reg_bound p k ==>
  ?ck t2. evaluate (comp jump off k p,t1 with clock := ck + t1.clock) = (r,t2) /\
    (case r of SOME(Halt _) => t2.ffi = s2.ffi
     | SOME TimeOut => t2.ffi = s2.ffi | SOME(FinalFFI _) => t2.ffi = s2.ffi
     | _ => state_rel jump off k s2 t2)) /\
(!res middle. evaluate(p,s)=(res,middle) /\ cont_loop res /\ middle.clock<>0 ==> (!r s2 t1 k off jump.
  evaluate ((Loop p),(dec_clock middle)) = (r,s2) /\ r <> SOME Error /\
  state_rel jump off k (dec_clock middle) t1 /\ reg_bound (Loop p) k ==>
  ?ck t2. evaluate (comp jump off k (Loop p),t1 with clock := ck + t1.clock) = (r,t2) /\
    (case r of SOME(Halt _) => t2.ffi = s2.ffi
     | SOME TimeOut => t2.ffi = s2.ffi | SOME(FinalFFI _) => t2.ffi = s2.ffi
     | _ => state_rel jump off k s2 t2))) ==>
(!r s2 t1 k off jump.
  evaluate ((Loop p),s) = (r,s2) /\ r <> SOME Error /\
  state_rel jump off k s t1 /\ reg_bound (Loop p) k ==>
  ?ck t2. evaluate (comp jump off k (Loop p),t1 with clock := ck + t1.clock) = (r,t2) /\
    (case r of SOME(Halt _) => t2.ffi = s2.ffi
     | SOME TimeOut => t2.ffi = s2.ffi | SOME(FinalFFI _) => t2.ffi = s2.ffi
     | _ => state_rel jump off k s2 t2))``,
  rpt strip_tac >>
simp [Once comp_def]
    \\ qpat_x_assum `evaluate _ = _` mp_tac
    \\ simp [Once evaluate_def,get_var_def]
    \\ pairarg_tac \\ gvs []
    \\ reverse IF_CASES_TAC
    >-
     (gvs [] \\ strip_tac \\ gvs []
      \\ Cases_on ‘res = SOME Error’ \\ gvs [reg_bound_def]
      \\ first_x_assum drule_all
      \\ strip_tac \\ simp [Once evaluate_def]
      \\ qexists ‘ck’ \\ simp []
      \\ Cases_on ‘res’ \\ gvs []
      \\ Cases_on ‘x’ \\ gvs []
      \\ rw [] \\ gvs [])
    \\ IF_CASES_TAC
    >-
     (gvs [] \\ strip_tac \\ gvs []
      \\ Cases_on ‘res = SOME Error’ \\ gvs [reg_bound_def]
      \\ first_x_assum drule_all
      \\ strip_tac \\ simp [Once evaluate_def]
      \\ qexists ‘ck’ \\ simp []
      \\ Cases_on ‘res’ \\ gvs [] \\ gvs [state_rel_def]
      \\ Cases_on ‘x’ \\ gvs [state_rel_def])
    \\ strip_tac \\ gvs []
    \\ Cases_on ‘res = SOME Error’ \\ gvs [reg_bound_def]
    \\ first_x_assum drule_all \\ strip_tac
    \\ ‘state_rel jump off k s1 t2’ by (imp_res_tac cont_loop_IMP \\ gvs [])
    \\ ‘state_rel jump off k (dec_clock s1) (dec_clock t2)’ by
     (pop_assum mp_tac \\ simp [state_rel_def,dec_clock_def,SF SFY_ss]
      \\ rw [] \\ gvs [])
    \\ gvs [STOP_def,reg_bound_def]
    \\ first_x_assum drule_all
    \\ strip_tac \\ fs [dec_clock_def]
    \\ simp [Once evaluate_def]
    \\ qpat_x_assum ‘evaluate _ = (res,t2)’ assume_tac
    \\ ‘res ≠ SOME TimeOut’ by (CCONTR_TAC \\ gvs [])
    \\ drule_all evaluate_add_clock \\ fs []
    \\ disch_then $ qspec_then ‘ck'’ assume_tac
    \\ ‘t2.clock ≠ 0’ by gvs [state_rel_def]
    \\ qexists_tac ‘ck+ck'’ \\ gvs []
    \\ gvs [STOP_def,dec_clock_def]
    \\ qpat_x_assum ‘evaluate (comp _ _ _ (Loop _), _) = _’ mp_tac
    \\ simp [Once comp_def]);
val _ = print("cc_loop_statement=" ^ term_to_string(concl cc_loop) ^ "\n");
val _ = print("cc_loop_proved=" ^ term_to_string(rhs(concl(EQT_INTRO cc_loop))) ^ "\n");
