(* Original comp_correct Seq case body on its scoped constructor statement. *)
load "preamble";
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble stack_removeProofTheory stackSemTheory stack_removeTheory stackPropsTheory;
val _ = Globals.linewidth := 20000;
val cc_seq = prove(``!p q s. (!r s2 t1 k off jump.
  evaluate (p,s) = (r,s2) /\ r <> SOME Error /\
  state_rel jump off k s t1 /\ reg_bound p k ==>
  ?ck t2. evaluate (comp jump off k p,t1 with clock := ck + t1.clock) = (r,t2) /\
    (case r of SOME(Halt _) => t2.ffi = s2.ffi
     | SOME TimeOut => t2.ffi = s2.ffi | SOME(FinalFFI _) => t2.ffi = s2.ffi
     | _ => state_rel jump off k s2 t2)) /\
(!middle. evaluate(p,s)=(NONE,middle) ==> (!r s2 t1 k off jump.
  evaluate (q,middle) = (r,s2) /\ r <> SOME Error /\
  state_rel jump off k middle t1 /\ reg_bound q k ==>
  ?ck t2. evaluate (comp jump off k q,t1 with clock := ck + t1.clock) = (r,t2) /\
    (case r of SOME(Halt _) => t2.ffi = s2.ffi
     | SOME TimeOut => t2.ffi = s2.ffi | SOME(FinalFFI _) => t2.ffi = s2.ffi
     | _ => state_rel jump off k s2 t2))) ==>
(!r s2 t1 k off jump.
  evaluate ((Seq p q),s) = (r,s2) /\ r <> SOME Error /\
  state_rel jump off k s t1 /\ reg_bound (Seq p q) k ==>
  ?ck t2. evaluate (comp jump off k (Seq p q),t1 with clock := ck + t1.clock) = (r,t2) /\
    (case r of SOME(Halt _) => t2.ffi = s2.ffi
     | SOME TimeOut => t2.ffi = s2.ffi | SOME(FinalFFI _) => t2.ffi = s2.ffi
     | _ => state_rel jump off k s2 t2))``,
  rpt strip_tac >>
full_simp_tac(srw_ss())[] \\ simp [Once comp_def]
    \\ full_simp_tac(srw_ss())[evaluate_def,reg_bound_def,LET_DEF]
    \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
    \\ reverse(Cases_on `res = NONE`) \\ full_simp_tac(srw_ss())[]
    >- (rpt var_eq_tac
      \\ first_x_assum old_drule >> simp[]
      \\ strip_tac >> full_simp_tac(srw_ss())[]
      \\ pop_assum mp_tac >> CASE_TAC
      \\ rpt var_eq_tac >> full_simp_tac(srw_ss())[]
      \\ strip_tac
      \\ qexists_tac`ck`\\simp[])
    \\ first_x_assum old_drule >> simp[] >> strip_tac
    \\ first_x_assum old_drule \\ simp[] \\ strip_tac
    \\ ntac 2 (pop_assum mp_tac)
    \\ old_drule (GEN_ALL evaluate_add_clock)
    \\ disch_then(qspec_then`ck'`mp_tac)
    \\ simp[] \\ ntac 3 strip_tac
    \\ qexists_tac`ck+ck'`\\simp[]);
val _ = print("cc_seq_statement=" ^ term_to_string(concl cc_seq) ^ "\n");
val _ = print("cc_seq_proved=" ^ term_to_string(rhs(concl(EQT_INTRO cc_seq))) ^ "\n");
