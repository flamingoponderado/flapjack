(* Direct HOL-EVAL rows for crep_to_loopProofScript.sml:368 survives_MAPi_Assign. *)
load "bossLib";
load "preamble";
load "loopLangTheory";
load "loopPropsTheory";
load "crep_to_loopTheory";
load "indexedListsTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crep_to_loopTheory;
open loopPropsTheory;
open indexedListsTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

(* survives n (nested_seq (MAPi (fn n => Assign (n + offset)) les)) *)

print_eval "survives_mapi_empty"
  ``loopProps$survives 0
      (loopLang$nested_seq
        (MAPi (\n. loopLang$Assign (n + 0)) []))``;

print_eval "survives_mapi_one"
  ``loopProps$survives 1
      (loopLang$nested_seq
        (MAPi (\n. loopLang$Assign (n + 3))
          [loopLang$Const (5w:8 word)]))``;

print_eval "survives_mapi_two"
  ``loopProps$survives 2
      (loopLang$nested_seq
        (MAPi (\n. loopLang$Assign (n + 1))
          [loopLang$Const (5w:8 word); loopLang$Var 7]))``;

print_eval "survives_mapi_three"
  ``loopProps$survives 9
      (loopLang$nested_seq
        (MAPi (\n. loopLang$Assign (n + 4))
          [loopLang$Var 9; loopLang$Const (0w:8 word); loopLang$Var 9]))``;