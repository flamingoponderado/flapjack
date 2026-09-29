(*
  Direct HOL-EVAL fixture for the wordSem carrier helpers ported in
  Flapjack/Compiler/Backend/Semantics/WordSem/State.lean
  (cakeml/compiler/backend/semantics/wordSemScript.sml:15-37, 230-237):
  buffer_flush, buffer_write and stack_size at 64-bit words.
*)
load "bossLib";
load "preamble";
load "wordSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open wordSemTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rhs (concl th));
    print "\n"
  end;

val cb = ``<| position := (8w:word64); buffer := [1w; 2w] : word8 list; space_left := 3 |>``;

val _ = print_eval "buffer_flush_hit" ``buffer_flush ^cb (8w:word64) 10w``;
val _ = print_eval "buffer_flush_miss" ``buffer_flush ^cb (8w:word64) 11w``;
val _ = print_eval "buffer_write_hit" ``buffer_write ^cb (10w:word64) (5w:word8)``;
val _ = print_eval "buffer_write_miss" ``buffer_write ^cb (9w:word64) (5w:word8)``;
val _ = print_eval "stack_size_two"
  ``stack_size [StackFrame (SOME 2) [] [] NONE;
                StackFrame (SOME 4) [] [] (SOME (1,2,3))] : num option``;
val _ = print_eval "stack_size_unbounded"
  ``stack_size [StackFrame (SOME 2) [] [] NONE;
                StackFrame NONE [] [] NONE] : num option``;
