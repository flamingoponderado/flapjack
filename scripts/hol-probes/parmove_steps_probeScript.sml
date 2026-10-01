load "bossLib";
load "preamble";
load "parmoveTheory";
open bossLib HolKernel Parse preamble parmoveTheory;
fun print_proved label q rule =
  let val th = prove(q, mp_tac rule >> simp[])
  in if aconv (concl th) q then (print(label ^ "="); print "T\n") else raise Fail label end;
val _ = print_proved "ps_remove" ``$step ([(SOME (1:num),SOME (1:num))],[],[]) ([],[],[])`` (Q.ISPECL [`SOME (1:num)`, `([]:(num option # num option) list)`, `([]:(num option # num option) list)`, `([]:(num option # num option) list)`, `([]:(num option # num option) list)`] (CONJUNCT1 step_rules));
val _ = print_proved "ps_start" ``$step ([(SOME (1:num),SOME (2:num))],[],[]) ([],[(SOME (1:num),SOME (2:num))],[])`` (Q.ISPECL [`SOME (1:num)`, `SOME (2:num)`, `([]:(num option # num option) list)`, `([]:(num option # num option) list)`, `([]:(num option # num option) list)`] (CONJUNCT1 (CONJUNCT2 step_rules)));
val _ = print_proved "ps_extend" ``$step ([(SOME (3:num),SOME (1:num))],[(SOME (1:num),SOME (2:num))],[]) ([],[(SOME (3:num),SOME (1:num));(SOME (1:num),SOME (2:num))],[])`` (Q.ISPECL [`SOME (1:num)`, `SOME (3:num)`, `SOME (2:num)`, `([]:(num option # num option) list)`, `([]:(num option # num option) list)`, `([]:(num option # num option) list)`, `([]:(num option # num option) list)`] (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 step_rules))));
val _ = print_proved "ps_save" ``$step ([],[(SOME (1:num),SOME (2:num))],[]) ([],[(SOME (1:num),NONE)],[(NONE,SOME (2:num))])`` (Q.ISPECL [`SOME (1:num)`, `SOME (2:num)`, `([]:(num option # num option) list)`, `([]:(num option # num option) list)`, `([]:(num option # num option) list)`] (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 (CONJUNCT2 step_rules)))));
val _ = print_proved "ps_emit_head" ``$step ([],[(SOME (3:num),SOME (1:num));(SOME (1:num),SOME (2:num))],[]) ([],[(SOME (1:num),SOME (2:num))],[(SOME (3:num),SOME (1:num))])`` (Q.ISPECL [`SOME (1:num)`, `SOME (3:num)`, `SOME (2:num)`, `SOME (1:num)`, `([]:(num option # num option) list)`, `([]:(num option # num option) list)`, `([]:(num option # num option) list)`] (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 (CONJUNCT2 (CONJUNCT2 step_rules))))));
val _ = print_proved "ps_emit_last" ``$step ([],[(SOME (1:num),SOME (2:num))],[]) ([],[],[(SOME (1:num),SOME (2:num))])`` (Q.ISPECL [`SOME (1:num)`, `SOME (2:num)`, `([]:(num option # num option) list)`, `([]:(num option # num option) list)`] (CONJUNCT2 (CONJUNCT2 (CONJUNCT2 (CONJUNCT2 (CONJUNCT2 step_rules))))));
