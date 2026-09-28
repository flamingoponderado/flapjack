(*
  Direct HOL-EVAL fixture for Pancake loopSem cut_state_def / cut_res_def at the
  key-0 inputs used by the exact-carrier Lean regression
  `Flapjack/Test/LoopSemCutParity.lean`.
  Reference: cakeml/pancake/semantics/loopSemScript.sml:182-197.
  The observations cover successful restriction, a missing live local, an empty
  live set, result short-circuiting, a failed cut, timeout local clearing, and
  successful restriction plus clock decrement.
*)
load "bossLib";
load "preamble";
load "../semantics/loopSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open loopSemTheory;

val s = ``(s:(32,'ffi) loopSem$state)``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val _ = print_eval "cut0_success_lookup"
  ``case loopSem$cut_state (insert 0 T LN)
      (^s with locals := insert 0 (Word 5w) LN) of
      NONE => NONE | SOME s' => lookup 0 s'.locals``
val _ = print_eval "cut0_missing"
  ``loopSem$cut_state (insert 0 T LN) (^s with locals := LN)``
val _ = print_eval "cut0_empty_live"
  ``case loopSem$cut_state LN (^s with locals := insert 0 (Word 5w) LN) of
      NONE => NONE | SOME s' => lookup 0 s'.locals``
val _ = print_eval "cut0_res_short_circuit"
  ``case loopSem$cut_res (insert 0 T LN)
      (SOME (Break 3), ^s with <| locals := insert 0 (Word 5w) LN; clock := 7 |>) of
      (res,s') => (res, lookup 0 s'.locals, s'.clock)``
val _ = print_eval "cut0_res_missing_error"
  ``case loopSem$cut_res (insert 0 T LN)
      (NONE, ^s with <| locals := LN; clock := 7 |>) of
      (res,s') => (res, lookup 0 s'.locals, s'.clock)``
val _ = print_eval "cut0_res_timeout"
  ``case loopSem$cut_res (insert 0 T LN)
      (NONE, ^s with <| locals := insert 0 (Word 5w) LN; clock := 0 |>) of
      (res,s') => (res, lookup 0 s'.locals, s'.clock)``
val _ = print_eval "cut0_res_decrement"
  ``case loopSem$cut_res (insert 0 T LN)
      (NONE, ^s with <| locals := insert 0 (Word 5w) LN; clock := 5 |>) of
      (res,s') => (res, lookup 0 s'.locals, s'.clock)``