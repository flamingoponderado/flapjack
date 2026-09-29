(*
  Direct HOL EVAL oracle for the initial constructor slice of the exact
  loop_to_word compiler at cakeml/pancake/loop_to_wordScript.sml:56-77.

  This fixture observes the compiler's returned label pair as well as each
  emitted Word program. The remaining comp_def constructors are intentionally
  outside this probe and the corresponding Lean helper remains untagged.
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

(* comp_def, loop_to_wordScript.sml:56-77 *)
print_eval "comp_skip" ``comp ^ctxt loopLang$Skip ^labels``;
print_eval "comp_assign" ``comp ^ctxt
  (loopLang$Assign 10 (loopLang$Var 10)) ^labels``;
print_eval "comp_addcarry_valid" ``comp ^ctxt
  (loopLang$Primitive [10;11] AddCarry [12;13;14]) ^labels``;
print_eval "comp_addcarry_bad_dest_arity" ``comp ^ctxt
  (loopLang$Primitive [10] AddCarry [12;13;14]) ^labels``;
print_eval "comp_addcarry_bad_argument_arity" ``comp ^ctxt
  (loopLang$Primitive [10;11] AddCarry [12;13]) ^labels``;
print_eval "comp_longmul" ``comp ^ctxt
  (loopLang$Arith (LLongMul 10 11 12 13)) ^labels``;
print_eval "comp_longdiv" ``comp ^ctxt
  (loopLang$Arith (LLongDiv 10 11 12 13 14)) ^labels``;
print_eval "comp_div" ``comp ^ctxt
  (loopLang$Arith (LDiv 10 12 13)) ^labels``;

(* comp_def simple control/result clauses, loop_to_wordScript.sml:96-110 *)
print_eval "comp_break" ``comp ^ctxt (loopLang$Break 5) ^labels``;
print_eval "comp_continue" ``comp ^ctxt (loopLang$Continue 6) ^labels``;
print_eval "comp_raise" ``comp ^ctxt (loopLang$Raise 10) ^labels``;
print_eval "comp_return" ``comp ^ctxt (loopLang$Return [10;11;12]) ^labels``;
print_eval "comp_tick" ``comp ^ctxt loopLang$Tick ^labels``;
print_eval "comp_fail" ``comp ^ctxt loopLang$Fail ^labels``;
print_eval "comp_locValue" ``comp ^ctxt (loopLang$LocValue 10 3) ^labels``;
