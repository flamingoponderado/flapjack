load "preamble";
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble stack_removeProofTheory stackSemTheory stack_removeTheory stackPropsTheory;
val _ = Globals.linewidth := 20000;
val ch = prove(``!s1 r s2 t1 k off jump bop dst src.
  stackSem$evaluate ((stackLang$OpCurrHeap bop dst src),s1) = (r,s2) /\ r <> SOME stackSem$Error /\
  state_rel jump off k s1 t1 /\ reg_bound (stackLang$OpCurrHeap bop dst src) k ==>
  ?ck t2. stackSem$evaluate (comp jump off k (stackLang$OpCurrHeap bop dst src),t1 with clock := ck + t1.clock) = (r,t2) /\
    (case r of SOME(stackSem$Halt _) => t2.ffi = s2.ffi
     | SOME stackSem$TimeOut => t2.ffi = s2.ffi
     | SOME(stackSem$FinalFFI _) => t2.ffi = s2.ffi
     | _ => state_rel jump off k s2 t2)``,
  rpt gen_tac >> strip_tac >> qexists_tac `0` >> simp [with_same_clock] >>
  `s1.use_store` by fs [state_rel_def] >>
  fs [comp_def,evaluate_def,reg_bound_def] >>
  gvs [AllCaseEqs(),word_exp_def] >> every_case_tac >> fs [] >> rw [] >>
  fs [inst_def,assign_def,word_exp_def] >>
  gvs [AllCaseEqs(),word_exp_def,PULL_EXISTS] >>
  rename [‘FLOOKUP s1.regs src = SOME (Word c1)’] >>
  rename [‘FLOOKUP s1.store CurrHeap = SOME (Word c2)’] >>
  qsuff_tac ‘FLOOKUP t1.regs src = SOME (Word c1) /\
             FLOOKUP t1.regs (k + 2) = SOME (Word c2)’ >- fs [] >>
  fs [state_rel_def]);
val _ = print("ch_statement=" ^ term_to_string(concl ch) ^ "\n");
val _ = print("ch_types=" ^ String.concatWith ";" (map (fn v => fst(dest_var v) ^ type_to_string(type_of v)) (fst(strip_forall(concl ch)))) ^ "\n");
val _ = print("ch_proved=" ^ term_to_string(rhs(concl(EQT_INTRO ch))) ^ "\n");
