load "preamble";
load "stackSemTheory";
open bossLib HolKernel Parse preamble stackSemTheory;
val _ = Globals.linewidth := 20000;
val cseq = prove(``!p q s res t.
  (!r u. evaluate(p,s)=(r,u) ==> u.clock<=s.clock) /\
  (!r u. fix_clock s (evaluate(p,s))=(r,u) /\ r=NONE ==>
    !r2 u2. evaluate(q,u)=(r2,u2) ==> u2.clock<=u.clock) /\
  evaluate(Seq p q,s)=(res,t) ==> t.clock<=s.clock``, rpt strip_tac >> qpat_x_assum `evaluate (_,_) = (_,_)` (fn th => ACCEPT_TAC (MATCH_MP evaluate_clock th)));
val _ = print("cseq_statement=" ^ term_to_string(concl cseq) ^ "\n");
val _ = print("cseq_proved=" ^ term_to_string(rhs(concl(EQT_INTRO cseq))) ^ "\n");
val cif = prove(``!cmp reg ri p q s res t.
  (!x y. get_var reg s=SOME x /\ get_var_imm ri s=SOME y /\ wordSem$word_cmp cmp x y=SOME T ==>
    !r u. evaluate(p,s)=(r,u) ==> u.clock<=s.clock) /\
  (!x y. get_var reg s=SOME x /\ get_var_imm ri s=SOME y /\ wordSem$word_cmp cmp x y=SOME F ==>
    !r u. evaluate(q,s)=(r,u) ==> u.clock<=s.clock) /\
  evaluate(If cmp reg ri p q,s)=(res,t) ==> t.clock<=s.clock``, rpt strip_tac >> qpat_x_assum `evaluate (_,_) = (_,_)` (fn th => ACCEPT_TAC (MATCH_MP evaluate_clock th)));
val _ = print("cif_statement=" ^ term_to_string(concl cif) ^ "\n");
val _ = print("cif_proved=" ^ term_to_string(rhs(concl(EQT_INTRO cif))) ^ "\n");
val cloop = prove(``!p s res t.
  (!r u. evaluate(p,s)=(r,u) ==> u.clock<=s.clock) /\
  (!r u. fix_clock s (evaluate(p,s))=(r,u) /\ cont_loop r /\ u.clock<>0 ==>
    !r2 u2. evaluate(Loop p,dec_clock u)=(r2,u2) ==> u2.clock<= (dec_clock u).clock) /\
  evaluate(Loop p,s)=(res,t) ==> t.clock<=s.clock``, rpt strip_tac >> qpat_x_assum `evaluate (_,_) = (_,_)` (fn th => ACCEPT_TAC (MATCH_MP evaluate_clock th)));
val _ = print("cloop_statement=" ^ term_to_string(concl cloop) ^ "\n");
val _ = print("cloop_proved=" ^ term_to_string(rhs(concl(EQT_INTRO cloop))) ^ "\n");
