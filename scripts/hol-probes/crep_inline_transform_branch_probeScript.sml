(* Direct original Pancake HOL EVAL rows for every clause of
   crep_inline$transform_branch_def (cakeml/pancake/crep_inlineScript.sml:155-164). *)

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

val _ = print_eval "transform_branch_return" ``transform_branch 2 [10] ^returned =
  Seq (Seq (Assign 10 (Var 2)) Skip) (Break 2)``;
val _ = print_eval "transform_branch_call_none" ``transform_branch 2 [10] ^call_none =
  Seq (Call (SOME ([10], NONE)) «f» [Var 2]) (Break 2)``;
val _ = print_eval "transform_branch_call_returns" ``transform_branch 2 [10] ^call_returns =
  ^call_returns``;
val _ = print_eval "transform_branch_call_handler" ``transform_branch 2 [10] ^handler =
  Call (SOME ([12], SOME ((3w:8 word),
    Seq (Seq (Assign 10 (Var 3)) Skip) (Break 2)))) «f» [Var 2]``;
val _ = print_eval "transform_branch_dec" ``transform_branch 2 [10] ^dec =
  Dec 1 (Const 1w) (Seq (Seq (Assign 10 (Var 2)) Skip) (Break 2))``;
val _ = print_eval "transform_branch_while" ``transform_branch 2 [10] ^whl =
  While (Const 1w) (Seq (Seq (Assign 10 (Var 2)) Skip) (Break 3))``;
val _ = print_eval "transform_branch_seq" ``transform_branch 2 [10] ^seq =
  Seq (Seq (Seq (Assign 10 (Var 2)) Skip) (Break 2)) Skip``;
val _ = print_eval "transform_branch_if" ``transform_branch 2 [10] ^ite =
  If (Const 1w) (Seq (Seq (Assign 10 (Var 2)) Skip) (Break 2)) Skip``;
val _ = print_eval "transform_branch_default"
  ``transform_branch 2 [10] (Skip : 8 crepLang$prog) = (Skip : 8 crepLang$prog)``;
