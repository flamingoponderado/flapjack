load "preamble";
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble stack_removeProofTheory stackSemTheory;
val _ = Globals.linewidth := 20000;
val _ = print("we_source=" ^ term_to_string(concl state_rel_word_exp) ^ "\n");
val we = prove(``!jump off k s t e w. state_rel jump off k s t /\ reg_bound_exp e k /\ word_exp s e = SOME w ==> word_exp t e = SOME w``,
  metis_tac [state_rel_word_exp]);
val _ = print("we_statement=" ^ term_to_string(concl we) ^ "\n");
val _ = print("we_types=" ^ String.concatWith ";" (map (fn v => fst(dest_var v) ^ type_to_string(type_of v)) (fst(strip_forall(concl we)))) ^ "\n");
val _ = print("we_proved=" ^ term_to_string(rhs(concl(EQT_INTRO we))) ^ "\n");
