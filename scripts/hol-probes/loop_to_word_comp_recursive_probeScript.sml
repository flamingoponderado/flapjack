(*
  Direct HOL EVAL oracle for the recursive constructor cases of
  loop_to_word$comp at cakeml/pancake/loop_to_wordScript.sml:107-120, 138.

  This probe isolates Seq, If, Loop, and Mark while also checking the returned
  threaded label pair. The partial Lean case slice is
  Flapjack.Pancake.LoopToWord.CompCases.Recursive.
*)
load "bossLib";
load "preamble";
load "loop_to_wordTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open loop_to_wordTheory;

fun print_eval label q =
  let val th = EVAL q in
    print (label ^ "="); print_term (rconc th); print "\n"
  end;

val ctxt = ``insert 14 28 (insert 13 26 (insert 12 24
  (insert 11 22 (insert 10 20 (LN : num num_map)))))``;
val labels = ``(7:num,11:num)``;
val live_in = ``insert 10 () (LN : num_set)``;
val live_out = ``insert 11 () (LN : num_set)``;

(* comp_def, Seq clause, loop_to_wordScript.sml:107-110 *)
print_eval "comp_seq" ``comp ^ctxt
  (loopLang$Seq (loopLang$Assign 10 (loopLang$Var 11))
    (loopLang$Assign 12 (loopLang$Const 5w))) ^labels``;

(* comp_def, If clause, loop_to_wordScript.sml:112-114 *)
print_eval "comp_if" ``comp ^ctxt
  (loopLang$If Equal 10 (Reg 11)
    (loopLang$Assign 12 (loopLang$Const 5w))
    (loopLang$Assign 13 (loopLang$Var 14))
    (insert 12 () (LN : num_set))) ^labels``;

(* comp_def, Loop clause, loop_to_wordScript.sml:116-120 *)
print_eval "comp_loop" ``comp ^ctxt
  (loopLang$Loop ^live_in (loopLang$Assign 12 (loopLang$Var 13)) ^live_out)
  ^labels``;

(* comp_def, Mark clause, loop_to_wordScript.sml:138 *)
print_eval "comp_mark" ``comp ^ctxt
  (loopLang$Mark (loopLang$Assign 10 (loopLang$Var 14))) ^labels``;
