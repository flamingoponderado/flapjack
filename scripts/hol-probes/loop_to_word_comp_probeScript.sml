(*
  Direct HOL EVAL oracle for the exact loop_to_word program compiler at
  cakeml/pancake/loop_to_wordScript.sml:56-149:

    comp_def (:56-149)

  This is intentionally a HOL script rather than a second implementation; the
  checked-in output is captured from a direct HOL invocation of this file.
  The kernel-checked Lean replay is
  Flapjack.Test.LoopToWordExactParity.
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

val ctxt = ``insert 3 9 (LN : num num_map)``;
val ln = ``(LN : num_set)``;

(* comp_def, loop_to_wordScript.sml:56-149 *)
print_eval "comp_skip" ``loop_to_word$comp ^ctxt loopLang$Skip (0:num,0:num)``;
print_eval "comp_assign"
  ``loop_to_word$comp ^ctxt (loopLang$Assign 3 (loopLang$Const (7w : 8 word))) (0:num,0:num)``;
print_eval "comp_seq"
  ``loop_to_word$comp ^ctxt
      (loopLang$Seq (loopLang$Assign 3 (loopLang$Const (1w : 8 word)))
                    (loopLang$Assign 3 (loopLang$Var 3))) (0:num,0:num)``;
print_eval "comp_return"
  ``loop_to_word$comp ^ctxt (loopLang$Return [3; 5]) (0:num,0:num)``;
print_eval "comp_break" ``loop_to_word$comp ^ctxt (loopLang$Break 2) (0:num,0:num)``;
print_eval "comp_continue" ``loop_to_word$comp ^ctxt (loopLang$Continue 1) (0:num,0:num)``;
print_eval "comp_if"
  ``loop_to_word$comp ^ctxt
      (loopLang$If Equal 3 (asm$Reg 3) loopLang$Skip loopLang$Skip ^ln) (0:num,0:num)``;
print_eval "comp_loop"
  ``loop_to_word$comp ^ctxt (loopLang$Loop ^ln loopLang$Skip ^ln) (0:num,0:num)``;
print_eval "comp_call_tail"
  ``loop_to_word$comp ^ctxt (loopLang$Call NONE NONE [] NONE) (0:num,0:num)``;
print_eval "comp_load32"
  ``loop_to_word$comp ^ctxt (loopLang$Load32 3 5) (0:num,0:num)``;