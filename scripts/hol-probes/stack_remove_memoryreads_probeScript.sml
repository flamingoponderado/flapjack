load "preamble";
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble stack_removeProofTheory stackSemTheory set_sepTheory;
val _ = Globals.linewidth := 20000;
fun statement label th = print(label ^ "=" ^ term_to_string(concl th) ^ "\n");
fun types label th = print(label ^ "=" ^ String.concatWith ";" (map (fn v => fst(dest_var v) ^ type_to_string(type_of v)) (fst(strip_forall(concl th)))) ^ "\n");
fun proved label th = print(label ^ "=" ^ term_to_string(rhs(concl(EQT_INTRO th))) ^ "\n");
val mr_graph = prove(``!m d p m1 d1 a. (memory m d * p) (fun2set (m1,d1)) /\ a IN d ==> a IN d1 /\ m1 a = m a``,
  simp [Once STAR_def,SPLIT_EQ,memory_def] >> fs [fun2set_def,SUBSET_DEF,PULL_EXISTS]);
val _ = statement "mr_graph" mr_graph;
val _ = types "mr_graph_types" mr_graph;
val _ = proved "mr_graph_proved" mr_graph;
val mr_read = prove(``!jump off k s t a. state_rel jump off k s t /\ a IN s.mdomain ==> a IN t.mdomain /\ t.memory a = s.memory a``,
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `state_rel _ _ _ _ _` mp_tac >>
  simp [Once state_rel_def] >> every_case_tac >> fs [] >> strip_tac >>
  fs [GSYM STAR_ASSOC] >> imp_res_tac mr_graph >> fs []);
val _ = statement "mr_read" mr_read;
val _ = types "mr_read_types" mr_read;
val _ = proved "mr_read_proved" mr_read;
val mr_load = prove(``!jump off k s t x w. state_rel jump off k s t /\ mem_load x s = SOME w ==> mem_load x t = SOME w``,
  rpt strip_tac >> fs [mem_load_def] >> imp_res_tac mr_read >> fs []);
val _ = statement "mr_load" mr_load;
val _ = types "mr_load_types" mr_load;
val _ = proved "mr_load_proved" mr_load;
