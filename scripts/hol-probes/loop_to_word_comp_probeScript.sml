(*
  Direct HOL EVAL oracle for the first two constructor slices of the exact
  loop_to_word compiler at cakeml/pancake/loop_to_wordScript.sml:56-108.

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
print_eval "comp_store" ``comp ^ctxt
  (loopLang$Store (loopLang$Var 10) 11) ^labels``;
print_eval "comp_setglobal" ``comp ^ctxt
  (loopLang$SetGlobal (5w : 5 word) (loopLang$Var 10)) ^labels``;
print_eval "comp_load32" ``comp ^ctxt
  (loopLang$Load32 12 13 : 8 word loopLang$prog) ^labels``;
print_eval "comp_loadbyte" ``comp ^ctxt
  (loopLang$LoadByte 13 12 : 8 word loopLang$prog) ^labels``;
print_eval "comp_store32" ``comp ^ctxt
  (loopLang$Store32 12 14 : 8 word loopLang$prog) ^labels``;
print_eval "comp_storebyte" ``comp ^ctxt
  (loopLang$StoreByte 13 11 : 8 word loopLang$prog) ^labels``;
