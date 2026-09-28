(*
  Direct HOL-EVAL fixture for Pancake crep_to_loop compile_prog_def.
  Reference: cakeml/pancake/crep_to_loopScript.sml:257-265.

  Observations cover a one-entry program with `first_name`-offset function
  numbering, the per-function `(GENLIST I o LENGTH) params` slot list, a body
  exercising `crep_arith$simp_prog` (a constant `Mul` folds to a `Const`),
  and the `loop_live$optimise` marker on the compiled loop program.
*)
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

val prog = ``[(«f», ([1;2] : num list),
               crepLang$Assign 1 (crepLang$Crepop crepLang$Mul
                  [crepLang$Const (2w : 8 word); crepLang$Const (3w : 8 word)]))]``;

val _ = print_eval "cp_fnums"
  ``MAP FST (compile_prog RISC_V ^prog)``;
val _ = print_eval "cp_params"
  ``MAP (FST o SND) (compile_prog RISC_V ^prog)``;
val _ = print_eval "cp_body"
  ``MAP (SND o SND) (compile_prog RISC_V ^prog)``;
val _ = print_eval "cp_length"
  ``LENGTH (compile_prog RISC_V ^prog)``;

val prog2 = ``[(«f», ([] : num list),
                crepLang$Call NONE «f» [crepLang$Const (7w : 8 word)])]``;

val _ = print_eval "cp_call_fnums"
  ``MAP FST (compile_prog RISC_V ^prog2)``;
val _ = print_eval "cp_call_params"
  ``MAP (FST o SND) (compile_prog RISC_V ^prog2)``;
val _ = print_eval "cp_call_body"
  ``MAP (SND o SND) (compile_prog RISC_V ^prog2)``;
val _ = print_eval "done" ``T``;
