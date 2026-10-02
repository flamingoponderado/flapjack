load "preamble";
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble stack_removeProofTheory stackSemTheory stackPropsTheory asmTheory;
val _ = Globals.linewidth := 20000;
fun statement label th = print(label ^ "=" ^ term_to_string(concl th) ^ "\n");
fun types label th = print(label ^ "=" ^ String.concatWith ";" (map (fn v => fst(dest_var v) ^ type_to_string(type_of v)) (fst(strip_forall(concl th)))) ^ "\n");
fun proved label th = print(label ^ "=" ^ term_to_string(rhs(concl(EQT_INTRO th))) ^ "\n");
val ar_div = prove(``!jump off k s t s1 r1 r2 r3. state_rel jump off k s t /\
  reg_bound_inst (Arith (Div r1 r2 r3)) k /\ inst (Arith (Div r1 r2 r3)) s = SOME s1 ==>
  ?t1. inst (Arith (Div r1 r2 r3)) t = SOME t1 /\ state_rel jump off k s1 t1``,
  rpt gen_tac >> strip_tac >> match_mp_tac (GEN_ALL state_rel_inst) >> qexists_tac `s` >> fs []);
val _ = statement "ar_div" ar_div;
val _ = types "ar_div_types" ar_div;
val _ = proved "ar_div_proved" ar_div;
val ar_carry = prove(``!jump off k s t s1 r1 r2 r3 r4. state_rel jump off k s t /\
  reg_bound_inst (Arith (AddCarry r1 r2 r3 r4)) k /\ inst (Arith (AddCarry r1 r2 r3 r4)) s = SOME s1 ==>
  ?t1. inst (Arith (AddCarry r1 r2 r3 r4)) t = SOME t1 /\ state_rel jump off k s1 t1``,
  rpt gen_tac >> strip_tac >> match_mp_tac (GEN_ALL state_rel_inst) >> qexists_tac `s` >> fs []);
val _ = statement "ar_carry" ar_carry;
val _ = types "ar_carry_types" ar_carry;
val _ = proved "ar_carry_proved" ar_carry;
val ar_add_overflow = prove(``!jump off k s t s1 r1 r2 r3 r4. state_rel jump off k s t /\
  reg_bound_inst (Arith (AddOverflow r1 r2 r3 r4)) k /\ inst (Arith (AddOverflow r1 r2 r3 r4)) s = SOME s1 ==>
  ?t1. inst (Arith (AddOverflow r1 r2 r3 r4)) t = SOME t1 /\ state_rel jump off k s1 t1``,
  rpt gen_tac >> strip_tac >> match_mp_tac (GEN_ALL state_rel_inst) >> qexists_tac `s` >> fs []);
val _ = statement "ar_add_overflow" ar_add_overflow;
val _ = types "ar_add_overflow_types" ar_add_overflow;
val _ = proved "ar_add_overflow_proved" ar_add_overflow;
val ar_sub_overflow = prove(``!jump off k s t s1 r1 r2 r3 r4. state_rel jump off k s t /\
  reg_bound_inst (Arith (SubOverflow r1 r2 r3 r4)) k /\ inst (Arith (SubOverflow r1 r2 r3 r4)) s = SOME s1 ==>
  ?t1. inst (Arith (SubOverflow r1 r2 r3 r4)) t = SOME t1 /\ state_rel jump off k s1 t1``,
  rpt gen_tac >> strip_tac >> match_mp_tac (GEN_ALL state_rel_inst) >> qexists_tac `s` >> fs []);
val _ = statement "ar_sub_overflow" ar_sub_overflow;
val _ = types "ar_sub_overflow_types" ar_sub_overflow;
val _ = proved "ar_sub_overflow_proved" ar_sub_overflow;
val ar_longmul = prove(``!jump off k s t s1 r1 r2 r3 r4. state_rel jump off k s t /\
  reg_bound_inst (Arith (LongMul r1 r2 r3 r4)) k /\ inst (Arith (LongMul r1 r2 r3 r4)) s = SOME s1 ==>
  ?t1. inst (Arith (LongMul r1 r2 r3 r4)) t = SOME t1 /\ state_rel jump off k s1 t1``,
  rpt gen_tac >> strip_tac >> match_mp_tac (GEN_ALL state_rel_inst) >> qexists_tac `s` >> fs []);
val _ = statement "ar_longmul" ar_longmul;
val _ = types "ar_longmul_types" ar_longmul;
val _ = proved "ar_longmul_proved" ar_longmul;
val ar_longdiv = prove(``!jump off k s t s1 r1 r2 r3 r4 r5. state_rel jump off k s t /\
  reg_bound_inst (Arith (LongDiv r1 r2 r3 r4 r5)) k /\ inst (Arith (LongDiv r1 r2 r3 r4 r5)) s = SOME s1 ==>
  ?t1. inst (Arith (LongDiv r1 r2 r3 r4 r5)) t = SOME t1 /\ state_rel jump off k s1 t1``,
  rpt gen_tac >> strip_tac >> match_mp_tac (GEN_ALL state_rel_inst) >> qexists_tac `s` >> fs []);
val _ = statement "ar_longdiv" ar_longdiv;
val _ = types "ar_longdiv_types" ar_longdiv;
val _ = proved "ar_longdiv_proved" ar_longdiv;
