(* Direct original Pancake HOL EVAL rows for crep_inline$inline_nontail_def
   (cakeml/pancake/crep_inlineScript.sml:193-201). *)

load "bossLib";
load "preamble";
load "crep_inlineTheory";
load "crepLangTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crep_inlineTheory;
open crepLangTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val body = ``(crepLang$Return [Var 8]) : 8 crepLang$prog``;
val args = ``[(Const (7w:8 word))]``;

val _ = print_eval "inline_nontail_scalar" ``inline_nontail ^body [10] [20] [30] ^args [5] =
  Dec 20 (Const 0w)
    (Seq (Dec 30 (Const 7w) (Dec 5 (Var 30) ^body))
      (Seq (Assign 10 (Var 20)) Skip))``;
val _ = print_eval "inline_nontail_map2_truncates"
  ``inline_nontail ^body [10; 11] [20] [30] ^args [5] =
  Dec 20 (Const 0w)
    (Seq (Dec 30 (Const 7w) (Dec 5 (Var 30) ^body))
      (Seq (Assign 10 (Var 20)) Skip))``;
val _ = print_eval "inline_nontail_arg_shape_mismatch"
  ``inline_nontail ^body [10] [20] [30] ^args [] =
  Dec 20 (Const 0w)
    (Seq (Dec 30 (Const 7w) Skip) (Seq (Assign 10 (Var 20)) Skip))``;
