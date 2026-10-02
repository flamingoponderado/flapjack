load "preamble";
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble stack_removeProofTheory stackSemTheory stack_removeTheory stackPropsTheory;
val _ = Globals.linewidth := 20000;
val ci = prove(``!s1 r s2 t1 k off jump i.
  stackSem$evaluate ((stackLang$Inst i),s1) = (r,s2) /\ r <> SOME stackSem$Error /\
  state_rel jump off k s1 t1 /\ reg_bound (stackLang$Inst i) k ==>
  ?ck t2. stackSem$evaluate (comp jump off k (stackLang$Inst i),t1 with clock := ck + t1.clock) = (r,t2) /\
    (case r of SOME(stackSem$Halt _) => t2.ffi = s2.ffi
     | SOME stackSem$TimeOut => t2.ffi = s2.ffi
     | SOME(stackSem$FinalFFI _) => t2.ffi = s2.ffi
     | _ => state_rel jump off k s2 t2)``,
  rpt gen_tac >> strip_tac >> qexists_tac `0` >> simp [with_same_clock] >>
  fs [comp_def,evaluate_def,reg_bound_def] >>
  every_case_tac >> fs [] >> imp_res_tac (GEN_ALL state_rel_inst) >> fs [] >>
  metis_tac [GEN_ALL state_rel_inst]);
val _ = print("ci_statement=" ^ term_to_string(concl ci) ^ "\n");
val _ = print("ci_types=" ^ String.concatWith ";" (map (fn v => fst(dest_var v) ^ type_to_string(type_of v)) (fst(strip_forall(concl ci)))) ^ "\n");
val _ = print("ci_proved=" ^ term_to_string(rhs(concl(EQT_INTRO ci))) ^ "\n");
