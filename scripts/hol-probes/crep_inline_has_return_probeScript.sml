(* Direct original Pancake HOL EVAL rows for crep_inline$has_return_def
   (cakeml/pancake/crep_inlineScript.sml:41-50). *)

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

val _ = print_eval "has_return_return" ``has_return (Return [Var 2] : 8 crepLang$prog)``;
val _ = print_eval "has_return_call_none" ``has_return (Call NONE «f» [] : 8 crepLang$prog)``;
val _ = print_eval "has_return_call_dest" ``has_return (Call (SOME ([10], NONE)) «f» [] : 8 crepLang$prog)``;
val _ = print_eval "has_return_call_handler"
  ``has_return (Call (SOME ([], SOME ((3w:8 word), Return [Var 2]))) «f» [] : 8 crepLang$prog)``;
val _ = print_eval "has_return_dec"
  ``has_return (Dec 1 (Const (1w:8 word)) (Return [Var 2]) : 8 crepLang$prog)``;
val _ = print_eval "has_return_seq"
  ``has_return (Seq Skip (Return [Var 2]) : 8 crepLang$prog)``;
val _ = print_eval "has_return_if"
  ``has_return (If (Const (1w:8 word)) Skip (Return [Var 2]) : 8 crepLang$prog)``;
val _ = print_eval "has_return_while"
  ``has_return (While (Const (1w:8 word)) (Return [Var 2]) : 8 crepLang$prog)``;
val _ = print_eval "has_return_default" ``has_return (Skip : 8 crepLang$prog)``;
