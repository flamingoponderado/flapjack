(* Literal original If case body with its actual source-guarded IHs. *)
load "preamble";
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble stack_removeProofTheory stackSemTheory stack_removeTheory stackPropsTheory;
val _ = Globals.linewidth := 20000;
val state_rel_get_var = prove(``!jump off k s t n. state_rel jump off k s t /\ n < k ==> get_var n s = get_var n t``,
  rpt strip_tac >> fs [state_rel_def,get_var_def] >> metis_tac []);
val cc_if = prove(``!cmp reg ri p q s. (!left right. get_var reg s=SOME left /\ get_var_imm ri s=SOME right /\ wordSem$word_cmp cmp left right=SOME T ==> (!r s2 t1 k off jump.
  evaluate (p,s) = (r,s2) /\ r <> SOME Error /\
  state_rel jump off k s t1 /\ reg_bound p k ==>
  ?ck t2. evaluate (comp jump off k p,t1 with clock := ck + t1.clock) = (r,t2) /\
    (case r of SOME(Halt _) => t2.ffi = s2.ffi
     | SOME TimeOut => t2.ffi = s2.ffi | SOME(FinalFFI _) => t2.ffi = s2.ffi
     | _ => state_rel jump off k s2 t2))) /\
(!left right. get_var reg s=SOME left /\ get_var_imm ri s=SOME right /\ wordSem$word_cmp cmp left right=SOME F ==> (!r s2 t1 k off jump.
  evaluate (q,s) = (r,s2) /\ r <> SOME Error /\
  state_rel jump off k s t1 /\ reg_bound q k ==>
  ?ck t2. evaluate (comp jump off k q,t1 with clock := ck + t1.clock) = (r,t2) /\
    (case r of SOME(Halt _) => t2.ffi = s2.ffi
     | SOME TimeOut => t2.ffi = s2.ffi | SOME(FinalFFI _) => t2.ffi = s2.ffi
     | _ => state_rel jump off k s2 t2))) ==>
(!r s2 t1 k off jump.
  evaluate ((If cmp reg ri p q),s) = (r,s2) /\ r <> SOME Error /\
  state_rel jump off k s t1 /\ reg_bound (If cmp reg ri p q) k ==>
  ?ck t2. evaluate (comp jump off k (If cmp reg ri p q),t1 with clock := ck + t1.clock) = (r,t2) /\
    (case r of SOME(Halt _) => t2.ffi = s2.ffi
     | SOME TimeOut => t2.ffi = s2.ffi | SOME(FinalFFI _) => t2.ffi = s2.ffi
     | _ => state_rel jump off k s2 t2))``,
  rpt strip_tac >>
full_simp_tac(srw_ss())[] \\ simp [Once comp_def]
    \\ full_simp_tac(srw_ss())[evaluate_def,reg_bound_def]
    \\ imp_res_tac state_rel_get_var \\ full_simp_tac(srw_ss())[]
    \\ qpat_x_assum`_ = (r,_)`mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ strip_tac \\ full_simp_tac(srw_ss())[] \\ rev_full_simp_tac(srw_ss())[]
    \\ first_x_assum old_drule \\ simp[] \\ strip_tac
    \\ qexists_tac`ck` \\ simp[]
    \\ full_simp_tac(srw_ss())[get_var_def]
    \\ Cases_on `ri` \\ full_simp_tac(srw_ss())[get_var_imm_def]
    \\ imp_res_tac state_rel_get_var \\ full_simp_tac(srw_ss())[]);
val _ = print("cc_if_statement=" ^ term_to_string(concl cc_if) ^ "\n");
val _ = print("cc_if_proved=" ^ term_to_string(rhs(concl(EQT_INTRO cc_if))) ^ "\n");
