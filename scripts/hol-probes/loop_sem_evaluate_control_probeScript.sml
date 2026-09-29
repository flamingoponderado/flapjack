(*
  Direct HOL-EVAL fixture for the control clauses of Pancake loopSem
  evaluate_def (cakeml/pancake/semantics/loopSemScript.sml:278-440):
  If with cut_res, Loop (Break 0, Continue, Return, timeout, outer Break),
  non-tail Call with return values, with a return handler and with an
  exception handler, Raise, Primitive AddCarry, LocValue and the empty-name
  FFI call.  Only fields fixed by each input state are projected.
*)
load "bossLib";
load "preamble";
load "../semantics/loopSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open loopSemTheory;

val s = ``(s:(8,'ffi) loopSem$state)``;

(* loopSem's evaluate_def is not in the default compset; register it so
   computeLib's EVAL, which reduces case scrutinees before branches, unfolds
   the recursive Loop/Call clauses only along the executed path. *)
val _ = computeLib.add_funs [evaluate_def];
fun print_eval label q =
  (print (label ^ "="); print_term (rconc (EVAL q)); print "\n")

val l17 = ``insert 1 (Word (7w : 8 word)) LN``;

val _ = print_eval "if_true"
  ``case loopSem$evaluate
      (If Equal 1 (Imm 7w) (Assign 2 (Const 1w)) (Assign 2 (Const 2w)) (insert 2 () LN),
       ^s with <|locals := ^l17; clock := 5|>) of
      (res,s') => (res, lookup 2 s'.locals, lookup 1 s'.locals, s'.clock)``
val _ = print_eval "if_false"
  ``case loopSem$evaluate
      (If Equal 1 (Imm 8w) (Assign 2 (Const 1w)) (Assign 2 (Const 2w)) (insert 2 () LN),
       ^s with <|locals := ^l17; clock := 5|>) of
      (res,s') => (res, lookup 2 s'.locals, lookup 1 s'.locals, s'.clock)``
val _ = print_eval "if_cut_error"
  ``case loopSem$evaluate
      (If Equal 1 (Imm 7w) Skip Skip (insert 9 () LN),
       ^s with <|locals := ^l17; clock := 5|>) of
      (res,s') => (res, lookup 1 s'.locals, s'.clock)``
val _ = print_eval "if_nonword_left_error"
  ``case loopSem$evaluate
      (If Equal 1 (Imm 7w) Skip Skip (insert 1 () LN),
       ^s with <|locals := insert 1 (Loc 9 0) LN; clock := 5|>) of
      (res,s') => (res, lookup 1 s'.locals, s'.clock)``
val _ = print_eval "if_nonword_right_error"
  ``case loopSem$evaluate
      (If Equal 1 (Reg 2) Skip Skip (insert 1 () LN),
       ^s with <|locals := insert 2 (Loc 8 0) ^l17; clock := 5|>) of
      (res,s') => (res, lookup 1 s'.locals, lookup 2 s'.locals, s'.clock)``
val _ = print_eval "loop_break0"
  ``case loopSem$evaluate
      (Loop LN (Break 0) LN, ^s with <|locals := ^l17; clock := 5|>) of
      (res,s') => (res, lookup 1 s'.locals, s'.clock)``
val _ = print_eval "loop_return"
  ``case loopSem$evaluate
      (Loop (insert 1 () LN) (Return [1]) LN, ^s with <|locals := ^l17; clock := 5|>) of
      (res,s') => (res, lookup 1 s'.locals, s'.clock)``
val _ = print_eval "loop_timeout"
  ``case loopSem$evaluate
      (Loop LN Skip LN, ^s with <|locals := ^l17; clock := 2|>) of
      (res,s') => (res, lookup 1 s'.locals, s'.clock)``
val _ = print_eval "loop_continue0_timeout"
  ``case loopSem$evaluate
      (Loop LN (Continue 0) LN, ^s with <|locals := ^l17; clock := 1|>) of
      (res,s') => (res, lookup 1 s'.locals, s'.clock)``
val _ = print_eval "loop_break_outer"
  ``case loopSem$evaluate
      (Loop LN (Break 2) LN, ^s with <|locals := ^l17; clock := 5|>) of
      (res,s') => (res, lookup 1 s'.locals, s'.clock)``
val _ = print_eval "call_return"
  ``case loopSem$evaluate
      (Call (SOME ([3], insert 1 () LN)) (SOME 1) [1] NONE,
       ^s with <|locals := ^l17; code := insert 1 ([5], Return [5]) LN; clock := 5|>) of
      (res,s') => (res, lookup 3 s'.locals, lookup 1 s'.locals, s'.clock)``
val _ = print_eval "call_return_handler"
  ``case loopSem$evaluate
      (Call (SOME ([3], insert 1 () LN)) (SOME 1) [1]
         (SOME (4, Skip, Assign 6 (Var 3), insert 6 () LN)),
       ^s with <|locals := ^l17; code := insert 1 ([5], Return [5]) LN; clock := 5|>) of
      (res,s') => (res, lookup 6 s'.locals, lookup 1 s'.locals, s'.clock)``
val _ = print_eval "call_exception_handler"
  ``case loopSem$evaluate
      (Call (SOME ([3], insert 1 () LN)) (SOME 1) [1]
         (SOME (4, Assign 6 (Var 4), Skip, insert 6 () LN)),
       ^s with <|locals := ^l17; code := insert 1 ([5], Raise 5) LN; clock := 5|>) of
      (res,s') => (res, lookup 6 s'.locals, lookup 1 s'.locals, s'.clock)``
val _ = print_eval "call_exception_no_handler"
  ``case loopSem$evaluate
      (Call (SOME ([3], insert 1 () LN)) (SOME 1) [1] NONE,
       ^s with <|locals := ^l17; code := insert 1 ([5], Raise 5) LN; clock := 5|>) of
      (res,s') => (res, lookup 1 s'.locals, s'.clock)``
val _ = print_eval "call_arity_error"
  ``case loopSem$evaluate
      (Call (SOME ([3; 4], insert 1 () LN)) (SOME 1) [1] NONE,
       ^s with <|locals := ^l17; code := insert 1 ([5], Return [5]) LN; clock := 5|>) of
      (res,s') => (res, lookup 1 s'.locals, s'.clock)``
val _ = print_eval "tail_call_return"
  ``case loopSem$evaluate
      (Call NONE (SOME 1) [1] NONE,
       ^s with <|locals := ^l17; code := insert 1 ([5], Return [5]) LN; clock := 5|>) of
      (res,s') => (res, lookup 1 s'.locals, s'.clock)``
val _ = print_eval "raise"
  ``case loopSem$evaluate (Raise 1, ^s with <|locals := ^l17; clock := 5|>) of
      (res,s') => (res, lookup 1 s'.locals, s'.clock)``
val _ = print_eval "primitive_add_carry"
  ``case loopSem$evaluate
      (Primitive [2; 3] AddCarry [1; 1; 1], ^s with <|locals := ^l17; clock := 5|>) of
      (res,s') => (res, lookup 2 s'.locals, lookup 3 s'.locals, s'.clock)``
val _ = print_eval "loc_value"
  ``case loopSem$evaluate
      (LocValue 2 1, ^s with <|locals := ^l17; code := insert 1 ([], Skip) LN; clock := 5|>) of
      (res,s') => (res, lookup 2 s'.locals, s'.clock)``
val _ = print_eval "loc_value_missing"
  ``case loopSem$evaluate
      (LocValue 2 3, ^s with <|locals := ^l17; code := insert 1 ([], Skip) LN; clock := 5|>) of
      (res,s') => (res, lookup 2 s'.locals, s'.clock)``
val _ = print_eval "ffi_empty_name"
  ``case loopSem$evaluate
      (FFI (strlit "") 2 2 2 2 (insert 2 () LN),
       ^s with <|locals := insert 2 (Word (0w : 8 word)) ^l17; clock := 5|>) of
      (res,s') => (res, lookup 2 s'.locals, lookup 1 s'.locals, s'.clock)``
