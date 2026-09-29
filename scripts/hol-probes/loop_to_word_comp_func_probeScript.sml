(*
  Direct HOL EVAL oracle for the loop_to_word executable entry points
  `comp_func`, `compile_prog`, and `compile`
  (cakeml/pancake/loop_to_wordScript.sml:164-177).

  Unlike the `comp` probes, these rows exercise the whole per-function
  compiler: `comp_func` computes the extra temporaries via
  `difference (acc_vars body LN) (toNumSet params)`, builds the dense context
  with `make_ctxt 2 (params ++ vs) LN`, and returns `FST (comp ctxt body
  (name,2))`; `compile_prog` maps that over the code list with
  `LENGTH params + 1`; `compile` is `compile_prog`.

  The Lean replay of these rows goes through the tagged exact
  `loopToWordCompFuncHOL` / `loopToWordCompileProgHOL` / `loopToWordCompileHOL`
  in Flapjack/Pancake/LoopToWord/CompFuncExact.lean.
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

(* comp_func_def, loop_to_wordScript.sml:164-169 *)
print_eval "comp_func_skip" ``comp_func (3:num) ([4;5] : num list)
  (loopLang$Skip : 8 word loopLang$prog)``;
print_eval "comp_func_param_assign" ``comp_func (6:num) ([7] : num list)
  (loopLang$Assign 7 (loopLang$Var 7) : 8 word loopLang$prog)``;
print_eval "comp_func_new_temp" ``comp_func (20:num) ([] : num list)
  (loopLang$Assign 9 (loopLang$Var 9) : 8 word loopLang$prog)``;

(* compile_prog_def / compile_def, loop_to_wordScript.sml:171-177 *)
val code = ``[((3:num), ([4;5] : num list), (loopLang$Skip : 8 word loopLang$prog));
              ((6:num), ([7] : num list), (loopLang$Assign 7 (loopLang$Var 7) : 8 word loopLang$prog));
              ((20:num), ([] : num list), (loopLang$Assign 9 (loopLang$Var 9) : 8 word loopLang$prog))]``;
print_eval "compile_prog_code" ``compile_prog ^code``;
print_eval "compile_code" ``compile ^code``;
