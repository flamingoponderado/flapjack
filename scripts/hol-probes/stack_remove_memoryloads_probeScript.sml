load "preamble";
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble stack_removeProofTheory stackSemTheory set_sepTheory wordSemTheory;
val _ = Globals.linewidth := 20000;
fun statement label th = print(label ^ "=" ^ term_to_string(concl th) ^ "\n");
fun types label th = print(label ^ "=" ^ String.concatWith ";" (map (fn v => fst(dest_var v) ^ type_to_string(type_of v)) (fst(strip_forall(concl th)))) ^ "\n");
fun proved label th = print(label ^ "=" ^ term_to_string(rhs(concl(EQT_INTRO th))) ^ "\n");
val mr_graph = prove(``!m d p m1 d1 a. (memory m d * p) (fun2set (m1,d1)) /\ a IN d ==> a IN d1 /\ m1 a = m a``,
  simp [Once STAR_def,SPLIT_EQ,memory_def] >> fs [fun2set_def,SUBSET_DEF,PULL_EXISTS]);
val mr_read = prove(``!jump off k s t a. state_rel jump off k s t /\ a IN s.mdomain ==> a IN t.mdomain /\ t.memory a = s.memory a``,
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `state_rel _ _ _ _ _` mp_tac >>
  simp [Once state_rel_def] >> every_case_tac >> fs [] >> strip_tac >>
  fs [GSYM STAR_ASSOC] >> imp_res_tac mr_graph >> fs []);
val ml_32 = prove(``!jump off k s t a x. state_rel jump off k s t /\
  mem_load_32 s.memory s.mdomain s.be a = SOME x ==>
  mem_load_32 t.memory t.mdomain t.be a = SOME x``,
  full_simp_tac(srw_ss())[wordSemTheory.mem_load_32_alt] >> srw_tac[][] >>
  `s.be = t.be` by full_simp_tac(srw_ss())[state_rel_def] >>
  ntac 5 (FULL_CASE_TAC >> fs[]) >> gvs[] >>
  full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  imp_res_tac mr_read >> full_simp_tac(srw_ss())[] >>
  rev_full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[]);
val _ = statement "ml_32" ml_32;
val _ = types "ml_32_types" ml_32;
val _ = proved "ml_32_proved" ml_32;
val ml_byte = prove(``!jump off k s t a x. state_rel jump off k s t /\
  mem_load_byte_aux s.memory s.mdomain s.be a = SOME x ==>
  mem_load_byte_aux t.memory t.mdomain t.be a = SOME x``,
  full_simp_tac(srw_ss())[wordSemTheory.mem_load_byte_aux_def] >> srw_tac[][] >>
  `s.be = t.be` by full_simp_tac(srw_ss())[state_rel_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  imp_res_tac mr_read >> full_simp_tac(srw_ss())[] >>
  rev_full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[]);
val _ = statement "ml_byte" ml_byte;
val _ = types "ml_byte_types" ml_byte;
val _ = proved "ml_byte_proved" ml_byte;
