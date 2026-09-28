(* Direct HOL-EVAL cases for the full crep_to_loop$compile_def. *)
load "bossLib";
load "preamble";
load "crep_to_loopTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crep_to_loopTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val ctxt = ``context
  (FEMPTY |+ (1, 7) |+ (2, 8) |+ (3, 9) |+ (4, 10))
  (FEMPTY |+ (strlit "f", (42, 2))) 4 RISC_V``;
val live = ``insert 2 () (insert 1 () LN)``;

val _ = print_eval "loop_nested_seq_empty"
  ``loopLang$nested_seq ([] : (8 word loopLang$prog) list)``;
val _ = print_eval "loop_nested_seq_one"
  ``loopLang$nested_seq
      [loopLang$Break 3 : 8 word loopLang$prog]``;
val _ = print_eval "loop_nested_seq_two"
  ``loopLang$nested_seq
      [loopLang$Break 3 : 8 word loopLang$prog; loopLang$Tick]``;

val _ = print_eval "compile_skip"
  ``compile ^ctxt ^live (crepLang$Skip : 8 word crepLang$prog)``;
val _ = print_eval "compile_break"
  ``compile ^ctxt ^live (crepLang$Break 3 : 8 word crepLang$prog)``;
val _ = print_eval "compile_continue"
  ``compile ^ctxt ^live (crepLang$Continue 4 : 8 word crepLang$prog)``;
val _ = print_eval "compile_tick"
  ``compile ^ctxt ^live (crepLang$Tick : 8 word crepLang$prog)``;
val _ = print_eval "compile_return"
  ``compile ^ctxt ^live (crepLang$Return [crepLang$Const (5w : 8 word)])``;
val _ = print_eval "compile_raise"
  ``compile ^ctxt ^live (crepLang$Raise (6w : 8 word))``;
val _ = print_eval "compile_shmem"
  ``compile ^ctxt ^live
      (crepLang$ShMem asm$Load8 1 (crepLang$Const (7w : 8 word)))``;
val _ = print_eval "compile_store"
  ``compile ^ctxt ^live
      (crepLang$Store (crepLang$Const (8w : 8 word)) (crepLang$Const 9w))``;
val _ = print_eval "compile_store32"
  ``compile ^ctxt ^live
      (crepLang$Store32 (crepLang$Const (10w : 8 word)) (crepLang$Const 11w))``;
val _ = print_eval "compile_store_byte"
  ``compile ^ctxt ^live
      (crepLang$StoreByte (crepLang$Const (12w : 8 word)) (crepLang$Const 13w))``;
val _ = print_eval "compile_store_glob"
  ``compile ^ctxt ^live
      (crepLang$StoreGlob (3w : 5 word) (crepLang$Const (14w : 8 word)))``;
val _ = print_eval "compile_seq"
  ``compile ^ctxt ^live
      (crepLang$Seq (crepLang$Break 1) crepLang$Tick : 8 word crepLang$prog)``;
val _ = print_eval "compile_assign"
  ``compile ^ctxt ^live
      (crepLang$Assign 1 (crepLang$Var 2) : 8 word crepLang$prog)``;
val _ = print_eval "compile_primitive"
  ``compile ^ctxt ^live
      (crepLang$Primitive [1] panLang$AddCarry [2] : 8 word crepLang$prog)``;
val _ = print_eval "compile_dec"
  ``compile ^ctxt ^live
      (crepLang$Dec 5 (crepLang$Const (15w : 8 word))
        (crepLang$Assign 5 (crepLang$Var 5)))``;
val _ = print_eval "compile_if"
  ``compile ^ctxt ^live
      (crepLang$If (crepLang$Const (1w : 8 word))
        (crepLang$Break 2) crepLang$Tick)``;
val _ = print_eval "compile_while"
  ``compile ^ctxt ^live
      (crepLang$While (crepLang$Const (1w : 8 word)) (crepLang$Break 2))``;
val _ = print_eval "compile_call"
  ``compile ^ctxt ^live
      (crepLang$Call (SOME ([1], SOME (3w, crepLang$Break 7))) (strlit "f")
        [crepLang$Const (16w : 8 word)])``;
val _ = print_eval "compile_ext_call"
  ``compile ^ctxt ^live
      (crepLang$ExtCall (strlit "ffi") 1 2 3 4 : 8 word crepLang$prog)``;
