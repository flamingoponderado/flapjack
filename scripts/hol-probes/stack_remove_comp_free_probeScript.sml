load "preamble";
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble wordsTheory stack_removeProofTheory stack_removeTheory stackSemTheory stackPropsTheory stackLangTheory set_sepTheory;
val _ = temp_delsimps ["NORMEQ_CONV"];
val _ = diminish_srw_ss ["ABBREV"];
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"];
val _ = set_trace "BasicProvers.var_eq_old" 1;
val _ = Globals.linewidth := 20000;
val cf = prove(``!s1 r s2 t1 k off jump n.
  stackSem$evaluate ((stackLang$StackFree n : 'a stackLang$prog),(s1:('a,'b,'c)stackSem$state)) = (r,s2) /\ r <> SOME stackSem$Error /\
  state_rel jump off k s1 t1 /\ reg_bound (stackLang$StackFree n : 'a stackLang$prog) k ==>
  ?ck t2. stackSem$evaluate (comp jump off k (stackLang$StackFree n : 'a stackLang$prog),t1 with clock := ck + t1.clock) = (r,t2) /\
    (case r of SOME(stackSem$Halt _) => t2.ffi = s2.ffi
     | SOME stackSem$TimeOut => t2.ffi = s2.ffi
     | SOME(stackSem$FinalFFI _) => t2.ffi = s2.ffi
     | _ => state_rel jump off k s2 t2)``,
  rpt gen_tac >> strip_tac >>
simp[comp_def]
    \\ old_drule evaluate_stack_free
    \\ simp[]
    \\ disch_then old_drule
    \\ strip_tac \\ simp[]
    \\ asm_exists_tac \\ simp[]
    \\ fs[evaluate_def]
    \\ every_case_tac \\ fs[]);
val _ = print("cf_statement=" ^ term_to_string(concl cf) ^ "\n");
val _ = print("cf_proved=" ^ term_to_string(rhs(concl(EQT_INTRO cf))) ^ "\n");
