load "preamble";
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble stack_removeProofTheory;
val _ = Globals.linewidth := 20000;
val _ = print("mw_source=" ^ term_to_string(concl memory_write) ^ "\n");
val mw = prove(``!x y sd dm sm m p. x IN sd /\ x IN dm /\
  (memory sm sd * p) (fun2set (m,dm)) ==>
  (memory ((x =+ y) sm) sd * p) (fun2set ((x =+ y) m,dm))``,
  metis_tac [memory_write]);
val _ = print("mw_statement=" ^ term_to_string(concl mw) ^ "\n");
val _ = print("mw_types=" ^ String.concatWith ";" (map (fn v => fst(dest_var v) ^ type_to_string(type_of v)) (fst(strip_forall(concl mw)))) ^ "\n");
val _ = print("mw_proved=" ^ term_to_string(rhs(concl(EQT_INTRO mw))) ^ "\n");
