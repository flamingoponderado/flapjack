load "preamble";
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble wordsTheory stack_removeProofTheory stack_removeTheory stackSemTheory stackPropsTheory stackLangTheory set_sepTheory;
val _ = temp_delsimps ["NORMEQ_CONV"];
val _ = diminish_srw_ss ["ABBREV"];
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"];
val _ = set_trace "BasicProvers.var_eq_old" 1;
val _ = Globals.linewidth := 20000;
val ca = prove(``!s1 r s2 t1 k off jump n.
  stackSem$evaluate ((stackLang$StackAlloc n : 'a stackLang$prog),(s1:('a,'b,'c)stackSem$state)) = (r,s2) /\ r <> SOME stackSem$Error /\
  state_rel jump off k s1 t1 /\ reg_bound (stackLang$StackAlloc n : 'a stackLang$prog) k ==>
  ?ck t2. stackSem$evaluate (comp jump off k (stackLang$StackAlloc n : 'a stackLang$prog),t1 with clock := ck + t1.clock) = (r,t2) /\
    (case r of SOME(stackSem$Halt _) => t2.ffi = s2.ffi
     | SOME stackSem$TimeOut => t2.ffi = s2.ffi
     | SOME(stackSem$FinalFFI _) => t2.ffi = s2.ffi
     | _ => state_rel jump off k s2 t2)``,
  rpt gen_tac >> strip_tac >>
simp[comp_def]
    \\ old_drule evaluate_stack_alloc
    \\ simp[]
    \\ disch_then old_drule
    \\ strip_tac \\ simp[]
    \\ asm_exists_tac \\ simp[]
    \\ BasicProvers.CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[state_rel_def] );
val _ = print("ca_statement=" ^ term_to_string(concl ca) ^ "\n");
val _ = print("ca_proved=" ^ term_to_string(rhs(concl(EQT_INTRO ca))) ^ "\n");
