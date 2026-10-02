load "preamble";
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble stack_removeProofTheory stackSemTheory stackPropsTheory asmTheory;
val _ = Globals.linewidth := 20000;
val ifp = prove(``!jump off k (s:('a,'b,'c) stackSem$state) t s1 op. state_rel jump off k s t /\
  reg_bound_inst (FP op:'a inst) k /\ inst (FP op) s = SOME s1 ==>
  ?t1. inst (FP op) t = SOME t1 /\ state_rel jump off k s1 t1``,
  rpt gen_tac >> strip_tac >> match_mp_tac (GEN_ALL state_rel_inst) >> qexists_tac `s` >> fs []);
val _ = print("ifp_statement=" ^ term_to_string(concl ifp) ^ "\n");
val _ = print("ifp_types=" ^ String.concatWith ";" (map (fn v => fst(dest_var v) ^ type_to_string(type_of v)) (fst(strip_forall(concl ifp)))) ^ "\n");
val _ = print("ifp_proved=" ^ term_to_string(rhs(concl(EQT_INTRO ifp))) ^ "\n");
