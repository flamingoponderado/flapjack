load "preamble";
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble set_sepTheory;
val _ = Globals.linewidth := 20000;
val _ = print("sa_source=" ^ term_to_string(concl STAR_ASSOC) ^ "\n");
val sa = prove(``!p:'a set->bool q r. p * (q * r) = (p * q) * r``,
  metis_tac [STAR_ASSOC]);
val _ = print("sa_statement=" ^ term_to_string(concl sa) ^ "\n");
val _ = print("sa_types=" ^ String.concatWith ";" (map (fn v => fst(dest_var v) ^ type_to_string(type_of v)) (fst(strip_forall(concl sa)))) ^ "\n");
val _ = print("sa_proved=" ^ term_to_string(rhs(concl(EQT_INTRO sa))) ^ "\n");
