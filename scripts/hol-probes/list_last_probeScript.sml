load "preamble";
open HolKernel Parse bossLib preamble listTheory;
val _ = Globals.linewidth := 20000;
val _ = print ("last_definition=" ^ term_to_string(concl LAST_DEF) ^ "\n");
val _ = print ("last_type=" ^ type_to_string(type_of ``LAST``) ^ "\n");
val _ = print ("last_hypotheses=" ^ Int.toString(length(hyp LAST_DEF)) ^ "\n");
val _ = print ("last_cons_statement=" ^ term_to_string(concl LAST_CONS) ^ "\n");
val consProof = prove (concl LAST_CONS, REWRITE_TAC [LAST_DEF, NOT_CONS_NIL]);
val _ = print ("last_cons_hypotheses=" ^ Int.toString(length(hyp consProof)) ^ "\n");
val _ = print ("last_cons_proved=" ^ term_to_string(rhs(concl(EQT_INTRO consProof))) ^ "\n");
val totalProof = prove (``!l:'a list. LAST l = case l of [] => LAST [] | h::t => if t = [] then h else LAST t``,
  Cases >> simp [LAST_DEF]);
val _ = print ("last_total_statement=" ^ term_to_string(concl totalProof) ^ "\n");
val _ = print ("last_total_hypotheses=" ^ Int.toString(length(hyp totalProof)) ^ "\n");
val _ = print ("last_total_proved=" ^ term_to_string(rhs(concl(EQT_INTRO totalProof))) ^ "\n");
