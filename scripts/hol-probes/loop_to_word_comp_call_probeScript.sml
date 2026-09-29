(*
  Direct HOL EVAL oracle for the Call clauses of loop_to_word$comp at
  cakeml/pancake/loop_to_wordScript.sml:145-165.

  The probe isolates the tail-call, non-tail without handler, and
  non-tail with handler branches, checking the link slot 0, the computed
  live cutset, label threading, and the wrapped Tick. The partial Lean case
  slice is Flapjack.Pancake.LoopToWord.CompCases.Recursive.
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
val live = ``insert 12 () (LN : num_set)``;

(* comp_def, tail-call branch, loop_to_wordScript.sml:145-147 *)
print_eval "comp_call_tail" ``comp ^ctxt
  (loopLang$Call NONE (SOME 5) [10;11] NONE : 8 word loopLang$prog) ^labels``;

(* comp_def, non-tail call without handler, loop_to_wordScript.sml:148-155 *)
print_eval "comp_call_no_handler" ``comp ^ctxt
  (loopLang$Call (SOME ([12;13],^live)) (SOME 5) [10;11] NONE
     : 8 word loopLang$prog) ^labels``;

(* comp_def, non-tail call with handler, loop_to_wordScript.sml:156-166 *)
print_eval "comp_call_handler" ``comp ^ctxt
  (loopLang$Call (SOME ([12;13],^live)) (SOME 5) [10;11]
     (SOME (14,
       (loopLang$Assign 10 (loopLang$Var 11) : 8 word loopLang$prog),
       (loopLang$Assign 12 (loopLang$Const 5w) : 8 word loopLang$prog),
       insert 13 () (LN : num_set)))
     : 8 word loopLang$prog) ^labels``;
