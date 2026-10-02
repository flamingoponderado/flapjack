load "preamble";
load "set_sepTheory";
open bossLib HolKernel Parse preamble set_sepTheory;
val _ = Globals.linewidth := 20000;
val sc = GEN_ALL (prove(``    !p:'a set->bool q. p * q = q * p
``,
  REWRITE_TAC [STAR_def,SPLIT_def,DISJOINT_DEF]
  \\ METIS_TAC [UNION_COMM,INTER_COMM,CONJ_SYM,CONJ_ASSOC]
));
val _ = print("sc_statement=" ^ term_to_string(concl sc) ^ "\n");
val _ = print("sc_types=" ^ String.concatWith ";" (map (fn v => fst(dest_var v) ^ type_to_string(type_of v)) (fst(strip_forall(concl sc)))) ^ "\n");
val _ = print("sc_proved=" ^ term_to_string(rhs(concl(EQT_INTRO sc))) ^ "\n");
val sw = GEN_ALL (prove(``    !y a x p f. (one (a,x) * p) (fun2set (f,d)) ==> (p * one (a,y)) (fun2set ((a =+ y) f,d))
``,
  SIMP_TAC std_ss [one_STAR,IN_DEF,fun2set_thm,combinTheory.APPLY_UPDATE_THM]
  \\ ONCE_REWRITE_TAC [STAR_COMM]
  \\ SIMP_TAC std_ss [one_STAR,IN_DEF,fun2set_thm,combinTheory.APPLY_UPDATE_THM]
  \\ NTAC 4 STRIP_TAC \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> (t /\ p x ==> p y)``)
  \\ SIMP_TAC std_ss [EXTENSION] \\ Cases
  \\ SIMP_TAC std_ss [fun2set_thm,IN_DELETE]
  \\ SIMP_TAC std_ss [fun2set_thm,IN_DELETE,IN_DEF]
  \\ Cases_on `q = a` \\ ASM_SIMP_TAC std_ss [combinTheory.APPLY_UPDATE_THM]
  \\ METIS_TAC []
));
val _ = print("sw_statement=" ^ term_to_string(concl sw) ^ "\n");
val _ = print("sw_types=" ^ String.concatWith ";" (map (fn v => fst(dest_var v) ^ type_to_string(type_of v)) (fst(strip_forall(concl sw)))) ^ "\n");
val _ = print("sw_proved=" ^ term_to_string(rhs(concl(EQT_INTRO sw))) ^ "\n");
