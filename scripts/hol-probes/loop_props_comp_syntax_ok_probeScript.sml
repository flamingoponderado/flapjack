(* Direct HOL-EVAL fixture for loopProps$comp_syntax_ok_def. *)
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

val live8 = ``insert 8 () LN``;
val live3_8 = ``insert 3 () ^live8``;

val _ = print_eval "comp_syntax_if_fold"
  ``FOLDL (\sp n. insert n () sp) ^live8 [3]``;
val _ = print_eval "comp_syntax_if_exists"
  ``?ns. ^live3_8 = FOLDL (\sp n. insert n () sp) ^live8 ns``;

val _ = print_eval "comp_syntax_skip"
  ``comp_syntax_ok ^live8 (Skip : 8 loopLang$prog)``;
val _ = print_eval "comp_syntax_assign"
  ``comp_syntax_ok ^live8 (Assign 4 (Const (0w : 8 word)))``;
val _ = print_eval "comp_syntax_locvalue"
  ``comp_syntax_ok ^live8 (LocValue 3 4 : 8 loopLang$prog)``;
val _ = print_eval "comp_syntax_load32"
  ``comp_syntax_ok ^live8 (Load32 5 6 : 8 loopLang$prog)``;
val _ = print_eval "comp_syntax_loadbyte"
  ``comp_syntax_ok ^live8 (LoadByte 7 9 : 8 loopLang$prog)``;
val _ = print_eval "comp_syntax_loop_valid"
  ``comp_syntax_ok ^live8 (Loop ^live8 Skip ^live8 : 8 loopLang$prog)``;
val _ = print_eval "comp_syntax_loop_bad_input"
  ``comp_syntax_ok ^live8 (Loop LN Skip ^live8 : 8 loopLang$prog)``;
val _ = print_eval "comp_syntax_loop_bad_output"
  ``comp_syntax_ok ^live8 (Loop ^live8 Skip LN : 8 loopLang$prog)``;
val _ = print_eval "comp_syntax_seq_threaded"
  ``comp_syntax_ok ^live8
      (Seq (Assign 3 (Const (0w : 8 word)))
           (Loop ^live3_8 Skip ^live3_8))``;
val _ = print_eval "comp_syntax_seq_unthreaded"
  ``comp_syntax_ok ^live8
      (Seq (Assign 3 (Const (0w : 8 word)))
           (Loop ^live8 Skip ^live8))``;
val _ = print_eval "comp_syntax_if_extension"
  ``comp_syntax_ok ^live8
      (If Equal 1 (Reg 2) Skip (Assign 4 (Const (0w : 8 word)))
        ^live3_8 : 8 loopLang$prog)``;
val _ = print_eval "comp_syntax_if_bad_branch"
  ``comp_syntax_ok ^live8
      (If Equal 1 (Reg 2) (Loop LN Skip LN) Tick ^live8 : 8 loopLang$prog)``;
val _ = print_eval "comp_syntax_arith"
  ``comp_syntax_ok ^live8 (Arith (LDiv 7 8 9) : 8 loopLang$prog)``;
val _ = print_eval "comp_syntax_break"
  ``comp_syntax_ok ^live8 (Break 11 : 8 loopLang$prog)``;
val _ = print_eval "comp_syntax_default"
  ``comp_syntax_ok ^live8 (Call NONE NONE [] NONE : 8 loopLang$prog)``;
