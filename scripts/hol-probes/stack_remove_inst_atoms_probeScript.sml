load "preamble";
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble stack_removeProofTheory stackSemTheory stackPropsTheory asmTheory;
val _ = Globals.linewidth := 20000;
fun statement label th = print(label ^ "=" ^ term_to_string(concl th) ^ "\n");
fun types label th = print(label ^ "=" ^ String.concatWith ";" (map (fn v => fst(dest_var v) ^ type_to_string(type_of v)) (fst(strip_forall(concl th)))) ^ "\n");
fun proved label th = print(label ^ "=" ^ term_to_string(rhs(concl(EQT_INTRO th))) ^ "\n");
val _ = statement "ia_full" state_rel_inst;
val _ = types "ia_full_types" (GEN_ALL state_rel_inst);
val ia_skip = prove(``!jump off k (s:('a,'b,'c) stackSem$state) t s1. state_rel jump off k s t /\
  reg_bound_inst (Skip:'a inst) k /\ inst Skip s = SOME s1 ==>
  ?t1. inst Skip t = SOME t1 /\ state_rel jump off k s1 t1``, rpt gen_tac >> strip_tac >> match_mp_tac (GEN_ALL state_rel_inst) >> qexists_tac `s` >> fs [reg_bound_inst_def]);
val _ = statement "ia_skip" ia_skip;
val _ = types "ia_skip_types" ia_skip;
val _ = proved "ia_skip_proved" ia_skip;
val ia_const = prove(``!jump off k s t s1 r w. state_rel jump off k s t /\
  reg_bound_inst (Const r w) k /\ inst (Const r w) s = SOME s1 ==>
  ?t1. inst (Const r w) t = SOME t1 /\ state_rel jump off k s1 t1``, rpt gen_tac >> strip_tac >> match_mp_tac (GEN_ALL state_rel_inst) >> qexists_tac `s` >> fs [reg_bound_inst_def]);
val _ = statement "ia_const" ia_const;
val _ = types "ia_const_types" ia_const;
val _ = proved "ia_const_proved" ia_const;
