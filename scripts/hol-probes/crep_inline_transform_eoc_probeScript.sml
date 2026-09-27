(* Direct original Pancake HOL EVAL rows for every clause of
   crep_inline$transform_eoc_def (cakeml/pancake/crep_inlineScript.sml:137-145). *)

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

val returned = ``(crepLang$Return [Var 2; Var 3]) : 8 crepLang$prog``;
val call_none = ``(Call NONE «f» [Var 2]) : 8 crepLang$prog``;
val call_returns = ``(Call (SOME ([12], NONE)) «f» [Var 2]) : 8 crepLang$prog``;
val handler = ``(Call (SOME ([12], SOME ((3w:8 word), Return [Var 3])))
                       «f» [Var 2]) : 8 crepLang$prog``;
val dec = ``(Dec 1 (Const (1w:8 word)) (Return [Var 2])) : 8 crepLang$prog``;
val whl = ``(While (Const (1w:8 word)) (Return [Var 2])) : 8 crepLang$prog``;
val seq = ``(Seq (Return [Var 2]) Skip) : 8 crepLang$prog``;
val ite = ``(If (Const (1w:8 word)) (Return [Var 2]) Skip) : 8 crepLang$prog``;

val _ = print_eval "transform_eoc_return_zip" ``transform_eoc [10] ^returned =
  Seq (Assign 10 (Var 2)) Skip``;
val _ = print_eval "transform_eoc_call_none" ``transform_eoc [10] ^call_none =
  Call (SOME ([10], NONE)) «f» [Var 2]``;
val _ = print_eval "transform_eoc_call_returns" ``transform_eoc [10] ^call_returns =
  ^call_returns``;
val _ = print_eval "transform_eoc_call_handler" ``transform_eoc [10] ^handler =
  Call (SOME ([12], SOME ((3w:8 word), Seq (Assign 10 (Var 3)) Skip)))
    «f» [Var 2]``;
val _ = print_eval "transform_eoc_call_handler_value" ``transform_eoc [10] ^handler``;
val _ = print_eval "transform_eoc_dec" ``transform_eoc [10] ^dec =
  Dec 1 (Const 1w) (Seq (Assign 10 (Var 2)) Skip)``;
val _ = print_eval "transform_eoc_while" ``transform_eoc [10] ^whl =
  While (Const 1w) (Seq (Assign 10 (Var 2)) Skip)``;
val _ = print_eval "transform_eoc_seq" ``transform_eoc [10] ^seq =
  Seq (Seq (Assign 10 (Var 2)) Skip) Skip``;
val _ = print_eval "transform_eoc_if" ``transform_eoc [10] ^ite =
  If (Const 1w) (Seq (Assign 10 (Var 2)) Skip) Skip``;
val _ = print_eval "transform_eoc_default" ``transform_eoc [10] (Skip : 8 crepLang$prog) =
  (Skip : 8 crepLang$prog)``;
