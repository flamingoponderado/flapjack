(*
  Direct HOL EVAL oracle for the exact loop_to_word expression compiler at
  cakeml/pancake/loop_to_wordScript.sml:22-40:

    comp_exp_def (:22-40)

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

(* comp_exp_def, loop_to_wordScript.sml:22-40 *)
print_eval "comp_exp_const" ``comp_exp ^ctxt (loopLang$Const (7w : 8 word))``;
print_eval "comp_exp_var" ``comp_exp ^ctxt (loopLang$Var 3)``;
print_eval "comp_exp_var_miss" ``comp_exp ^ctxt (loopLang$Var 8)``;
print_eval "comp_exp_lookup" ``comp_exp ^ctxt (loopLang$Lookup (5w : 5 word))``;
print_eval "comp_exp_base_addr" ``comp_exp ^ctxt loopLang$BaseAddr``;
print_eval "comp_exp_top_addr" ``comp_exp ^ctxt loopLang$TopAddr``;
print_eval "comp_exp_load" ``comp_exp ^ctxt (loopLang$Load (loopLang$Var 3))``;
print_eval "comp_exp_shift"
  ``comp_exp ^ctxt (loopLang$Shift Lsl (loopLang$Var 3) (loopLang$Const (1w : 8 word)))``;
print_eval "comp_exp_op"
  ``comp_exp ^ctxt (loopLang$Op Add [loopLang$Var 3; loopLang$Const (1w : 8 word)])``;
