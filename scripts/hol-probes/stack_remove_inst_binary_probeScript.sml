load "preamble";
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble stack_removeProofTheory stackSemTheory stackPropsTheory asmTheory;
val _ = Globals.linewidth := 20000;
fun statement label th = print(label ^ "=" ^ term_to_string(concl th) ^ "\n");
fun types label th = print(label ^ "=" ^ String.concatWith ";" (map (fn v => fst(dest_var v) ^ type_to_string(type_of v)) (fst(strip_forall(concl th)))) ^ "\n");
fun proved label th = print(label ^ "=" ^ term_to_string(rhs(concl(EQT_INTRO th))) ^ "\n");
val ib_binop = prove(``!jump off k s t s1 bop r1 r2 ri. state_rel jump off k s t /\
  reg_bound_inst (Arith (Binop bop r1 r2 ri)) k /\ inst (Arith (Binop bop r1 r2 ri)) s = SOME s1 ==>
  ?t1. inst (Arith (Binop bop r1 r2 ri)) t = SOME t1 /\ state_rel jump off k s1 t1``,
  rpt gen_tac >> strip_tac >> match_mp_tac (GEN_ALL state_rel_inst) >> qexists_tac `s` >> fs []);
val _ = statement "ib_binop" ib_binop;
val _ = types "ib_binop_types" ib_binop;
val _ = proved "ib_binop_proved" ib_binop;
val ib_shift = prove(``!jump off k s t s1 sh r1 r2 ri. state_rel jump off k s t /\
  reg_bound_inst (Arith (Shift sh r1 r2 ri)) k /\ inst (Arith (Shift sh r1 r2 ri)) s = SOME s1 ==>
  ?t1. inst (Arith (Shift sh r1 r2 ri)) t = SOME t1 /\ state_rel jump off k s1 t1``,
  rpt gen_tac >> strip_tac >> match_mp_tac (GEN_ALL state_rel_inst) >> qexists_tac `s` >> fs []);
val _ = statement "ib_shift" ib_shift;
val _ = types "ib_shift_types" ib_shift;
val _ = proved "ib_shift_proved" ib_shift;
