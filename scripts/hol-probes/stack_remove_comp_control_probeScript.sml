load "preamble";
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble stack_removeProofTheory stackSemTheory stack_removeTheory stackPropsTheory;
val _ = Globals.linewidth := 20000;
fun statement label th = print(label ^ "=" ^ term_to_string(concl th) ^ "\n");
fun types label th = print(label ^ "=" ^ String.concatWith ";" (map (fn v => fst(dest_var v) ^ type_to_string(type_of v)) (fst(strip_forall(concl th)))) ^ "\n");
fun proved label th = print(label ^ "=" ^ term_to_string(rhs(concl(EQT_INTRO th))) ^ "\n");
val getvar = prove(``!jump off k s t n. state_rel jump off k s t /\ n < k ==> get_var n s = get_var n t``,
  rpt strip_tac >> fs [state_rel_def,get_var_def] >> metis_tac []);
val decclock = prove(``!jump off k s t. state_rel jump off k s t ==> state_rel jump off k (dec_clock s) (dec_clock t)``,
  rpt strip_tac >> fs [state_rel_def,dec_clock_def] >> metis_tac []);
val cc_tick = prove(``!s1 r s2 t1 k off jump.
  stackSem$evaluate ((stackLang$Tick),s1) = (r,s2) /\ r <> SOME stackSem$Error /\
  state_rel jump off k s1 t1 /\ reg_bound (stackLang$Tick) k ==>
  ?ck t2. stackSem$evaluate (comp jump off k (stackLang$Tick),t1 with clock := ck + t1.clock) = (r,t2) /\
    (case r of SOME(stackSem$Halt _) => t2.ffi = s2.ffi
     | SOME stackSem$TimeOut => t2.ffi = s2.ffi
     | SOME(stackSem$FinalFFI _) => t2.ffi = s2.ffi
     | _ => state_rel jump off k s2 t2)``,
  rpt strip_tac >> full_simp_tac(srw_ss())[comp_def,evaluate_def] >>
  `s1.clock = t1.clock` by full_simp_tac(srw_ss())[state_rel_def] >>
  full_simp_tac(srw_ss())[] >> qexists_tac `0` >> full_simp_tac(srw_ss())[] >>
  CASE_TAC >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  imp_res_tac decclock >> full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[state_rel_def]);
val _ = statement "cc_tick" cc_tick;
val _ = types "cc_tick_types" cc_tick;
val _ = proved "cc_tick_proved" cc_tick;
val cc_return = prove(``!s1 r s2 t1 k off jump n.
  stackSem$evaluate ((stackLang$Return n),s1) = (r,s2) /\ r <> SOME stackSem$Error /\
  state_rel jump off k s1 t1 /\ reg_bound (stackLang$Return n) k ==>
  ?ck t2. stackSem$evaluate (comp jump off k (stackLang$Return n),t1 with clock := ck + t1.clock) = (r,t2) /\
    (case r of SOME(stackSem$Halt _) => t2.ffi = s2.ffi
     | SOME stackSem$TimeOut => t2.ffi = s2.ffi
     | SOME(stackSem$FinalFFI _) => t2.ffi = s2.ffi
     | _ => state_rel jump off k s2 t2)``,
  rpt strip_tac >> full_simp_tac(srw_ss())[comp_def,evaluate_def,reg_bound_def] >>
  qexists_tac `0` >> imp_res_tac getvar >> full_simp_tac(srw_ss())[] >>
  BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
  BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
  BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
  BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
  BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[]);
val _ = statement "cc_return" cc_return;
val _ = types "cc_return_types" cc_return;
val _ = proved "cc_return_proved" cc_return;
val cc_raise = prove(``!s1 r s2 t1 k off jump n.
  stackSem$evaluate ((stackLang$Raise n),s1) = (r,s2) /\ r <> SOME stackSem$Error /\
  state_rel jump off k s1 t1 /\ reg_bound (stackLang$Raise n) k ==>
  ?ck t2. stackSem$evaluate (comp jump off k (stackLang$Raise n),t1 with clock := ck + t1.clock) = (r,t2) /\
    (case r of SOME(stackSem$Halt _) => t2.ffi = s2.ffi
     | SOME stackSem$TimeOut => t2.ffi = s2.ffi
     | SOME(stackSem$FinalFFI _) => t2.ffi = s2.ffi
     | _ => state_rel jump off k s2 t2)``,
  rpt strip_tac >> full_simp_tac(srw_ss())[comp_def,evaluate_def,reg_bound_def] >>
  qexists_tac `0` >> imp_res_tac getvar >> full_simp_tac(srw_ss())[] >>
  BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
  BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
  BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
  BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[]);
val _ = statement "cc_raise" cc_raise;
val _ = types "cc_raise_types" cc_raise;
val _ = proved "cc_raise_proved" cc_raise;
val cc_break = prove(``!s1 r s2 t1 k off jump n.
  stackSem$evaluate ((stackLang$Break n),s1) = (r,s2) /\ r <> SOME stackSem$Error /\
  state_rel jump off k s1 t1 /\ reg_bound (stackLang$Break n) k ==>
  ?ck t2. stackSem$evaluate (comp jump off k (stackLang$Break n),t1 with clock := ck + t1.clock) = (r,t2) /\
    (case r of SOME(stackSem$Halt _) => t2.ffi = s2.ffi
     | SOME stackSem$TimeOut => t2.ffi = s2.ffi
     | SOME(stackSem$FinalFFI _) => t2.ffi = s2.ffi
     | _ => state_rel jump off k s2 t2)``,
  rpt strip_tac >> gvs [comp_def,evaluate_def] >> gvs [state_rel_def,SF SFY_ss]);
val _ = statement "cc_break" cc_break;
val _ = types "cc_break_types" cc_break;
val _ = proved "cc_break_proved" cc_break;
val cc_continue = prove(``!s1 r s2 t1 k off jump n.
  stackSem$evaluate ((stackLang$Continue n),s1) = (r,s2) /\ r <> SOME stackSem$Error /\
  state_rel jump off k s1 t1 /\ reg_bound (stackLang$Continue n) k ==>
  ?ck t2. stackSem$evaluate (comp jump off k (stackLang$Continue n),t1 with clock := ck + t1.clock) = (r,t2) /\
    (case r of SOME(stackSem$Halt _) => t2.ffi = s2.ffi
     | SOME stackSem$TimeOut => t2.ffi = s2.ffi
     | SOME(stackSem$FinalFFI _) => t2.ffi = s2.ffi
     | _ => state_rel jump off k s2 t2)``,
  rpt strip_tac >> gvs [comp_def,evaluate_def] >> gvs [state_rel_def,SF SFY_ss]);
val _ = statement "cc_continue" cc_continue;
val _ = types "cc_continue_types" cc_continue;
val _ = proved "cc_continue_proved" cc_continue;
