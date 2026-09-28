(* Direct HOL-EVAL fixture for loopProps$survives_def. *)
load "bossLib";
load "preamble";
load "../semantics/loopPropsTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open loopPropsTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val live3 = ``insert 3 () LN``;

val _ = print_eval "if_hit"
  ``survives 3 ((If Equal 1 (Imm 0w) Skip Skip ^live3) : 8 loopLang$prog)``;
val _ = print_eval "if_miss"
  ``survives 4 ((If Equal 1 (Imm 0w) Skip Skip ^live3) : 8 loopLang$prog)``;
val _ = print_eval "loop_hit"
  ``survives 3 ((Loop ^live3 Skip ^live3) : 8 loopLang$prog)``;
val _ = print_eval "loop_miss_out"
  ``survives 3 ((Loop ^live3 Skip LN) : 8 loopLang$prog)``;
val _ = print_eval "call_hit"
  ``survives 3 ((Call (SOME ([], ^live3)) NONE [] NONE) : 8 loopLang$prog)``;
val _ = print_eval "call_miss"
  ``survives 3 ((Call (SOME ([], LN)) NONE [] NONE) : 8 loopLang$prog)``;
val _ = print_eval "call_handler_hit"
  ``survives 3 ((Call (SOME ([], ^live3)) NONE []
      (SOME (0, Skip, Tick, ^live3))) : 8 loopLang$prog)``;
val _ = print_eval "call_handler_miss_post"
  ``survives 3 ((Call (SOME ([], ^live3)) NONE []
      (SOME (0, Skip, Tick, LN))) : 8 loopLang$prog)``;
val _ = print_eval "ffi_hit"
  ``survives 3 ((FFI (strlit "f") 1 2 3 4 ^live3) : 8 loopLang$prog)``;
val _ = print_eval "ffi_miss"
  ``survives 3 ((FFI (strlit "f") 1 2 3 4 LN) : 8 loopLang$prog)``;
val _ = print_eval "mark_seq"
  ``survives 3 ((Mark (Seq Skip Tick)) : 8 loopLang$prog)``;
val _ = print_eval "call_default"
  ``survives 3 ((Call NONE NONE [] NONE) : 8 loopLang$prog)``;
val _ = print_eval "assign_default"
  ``survives 3 ((Assign 3 (Const (0w : 8 word))) : 8 loopLang$prog)``;
