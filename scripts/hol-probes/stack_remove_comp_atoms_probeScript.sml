load "preamble";
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble stack_removeProofTheory stackSemTheory stack_removeTheory stackPropsTheory;
val _ = Globals.linewidth := 20000;
fun statement label th = print(label ^ "=" ^ term_to_string(concl th) ^ "\n");
fun types label th = print(label ^ "=" ^ String.concatWith ";" (map (fn v => fst(dest_var v) ^ type_to_string(type_of v)) (fst(strip_forall(concl th)))) ^ "\n");
fun proved label th = print(label ^ "=" ^ term_to_string(rhs(concl(EQT_INTRO th))) ^ "\n");
val getvar = prove(``!jump off k s t n. state_rel jump off k s t /\ n < k ==> get_var n s = get_var n t``,
  rpt strip_tac >> fs [state_rel_def,get_var_def] >> metis_tac []);
val cc_skip = prove(``!s1 r s2 t1 k off jump.
  stackSem$evaluate ((stackLang$Skip),s1) = (r,s2) /\ r <> SOME stackSem$Error /\
  state_rel jump off k s1 t1 /\ reg_bound (stackLang$Skip) k ==>
  ?ck t2. stackSem$evaluate (comp jump off k (stackLang$Skip),t1 with clock := ck + t1.clock) = (r,t2) /\
    (case r of SOME(stackSem$Halt _) => t2.ffi = s2.ffi
     | SOME stackSem$TimeOut => t2.ffi = s2.ffi
     | SOME(stackSem$FinalFFI _) => t2.ffi = s2.ffi
     | _ => state_rel jump off k s2 t2)``,
  rpt strip_tac >>
  full_simp_tac(srw_ss())[comp_def,evaluate_def] >> rpt var_eq_tac >>
  qexists_tac `0` >> full_simp_tac(srw_ss())[]);
val _ = statement "cc_skip" cc_skip;
val _ = types "cc_skip_types" cc_skip;
val _ = proved "cc_skip_proved" cc_skip;
val cc_halt = prove(``!s1 r s2 t1 k off jump n.
  stackSem$evaluate ((stackLang$Halt n),s1) = (r,s2) /\ r <> SOME stackSem$Error /\
  state_rel jump off k s1 t1 /\ reg_bound (stackLang$Halt n) k ==>
  ?ck t2. stackSem$evaluate (comp jump off k (stackLang$Halt n),t1 with clock := ck + t1.clock) = (r,t2) /\
    (case r of SOME(stackSem$Halt _) => t2.ffi = s2.ffi
     | SOME stackSem$TimeOut => t2.ffi = s2.ffi
     | SOME(stackSem$FinalFFI _) => t2.ffi = s2.ffi
     | _ => state_rel jump off k s2 t2)``,
  rpt strip_tac >>
  full_simp_tac(srw_ss())[comp_def,evaluate_def,reg_bound_def] >>
  imp_res_tac getvar >> full_simp_tac(srw_ss())[] >>
  qexists_tac `0` >>
  BasicProvers.TOP_CASE_TAC >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
  BasicProvers.TOP_CASE_TAC >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[state_rel_def]);
val _ = statement "cc_halt" cc_halt;
val _ = types "cc_halt_types" cc_halt;
val _ = proved "cc_halt_proved" cc_halt;
val cc_alloc = prove(``!s1 r s2 t1 k off jump n.
  stackSem$evaluate ((stackLang$Alloc n),s1) = (r,s2) /\ r <> SOME stackSem$Error /\
  state_rel jump off k s1 t1 /\ reg_bound (stackLang$Alloc n) k ==>
  ?ck t2. stackSem$evaluate (comp jump off k (stackLang$Alloc n),t1 with clock := ck + t1.clock) = (r,t2) /\
    (case r of SOME(stackSem$Halt _) => t2.ffi = s2.ffi
     | SOME stackSem$TimeOut => t2.ffi = s2.ffi
     | SOME(stackSem$FinalFFI _) => t2.ffi = s2.ffi
     | _ => state_rel jump off k s2 t2)``,
  rpt strip_tac >>
  fs [comp_def,evaluate_def] >> fs [state_rel_def]);
val _ = statement "cc_alloc" cc_alloc;
val _ = types "cc_alloc_types" cc_alloc;
val _ = proved "cc_alloc_proved" cc_alloc;
