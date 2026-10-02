load "preamble";
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble stack_removeProofTheory stackSemTheory stackPropsTheory asmTheory;
val _ = Globals.linewidth := 20000;
val im = prove(``!jump off k s t s1 op r a. state_rel jump off k s t /\
  reg_bound_inst (Mem op r a) k /\ inst (Mem op r a) s = SOME s1 ==>
  ?t1. inst (Mem op r a) t = SOME t1 /\ state_rel jump off k s1 t1``,
  rpt gen_tac >> strip_tac >> match_mp_tac (GEN_ALL state_rel_inst) >> qexists_tac `s` >> fs []);
val _ = print("im_statement=" ^ term_to_string(concl im) ^ "\n");
val _ = print("im_types=" ^ String.concatWith ";" (map (fn v => fst(dest_var v) ^ type_to_string(type_of v)) (fst(strip_forall(concl im)))) ^ "\n");
val _ = print("im_proved=" ^ term_to_string(rhs(concl(EQT_INTRO im))) ^ "\n");
