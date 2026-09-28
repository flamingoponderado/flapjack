(* Direct HOL-EVAL observations for crep_to_loopProof$survives_MAPi_Assign. *)
load "bossLib";
load "preamble";
load "loopLangTheory";
load "loopPropsTheory";
load "rich_listTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open rich_listTheory;
open loopLangTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

(* `les` is inferred as `64 word exp list`, the expression element type
   required by `Assign` in the source theorem. *)
val _ = print_eval "survives_mapi_assign_nil"
  ``loopProps$survives 4
      (loopLang$nested_seq (MAPi
        (\i (e : 64 word loopLang$exp). loopLang$Assign (i + 3) e) []))``;
val _ = print_eval "survives_mapi_assign_one"
  ``loopProps$survives 9
      (loopLang$nested_seq (MAPi
        (\i (e : 64 word loopLang$exp). loopLang$Assign (i + 5) e)
        [loopLang$Var 0]))``;
val _ = print_eval "survives_mapi_assign_three"
  ``loopProps$survives 17
      (loopLang$nested_seq (MAPi
        (\i (e : 64 word loopLang$exp). loopLang$Assign (i + 7) e)
        [loopLang$Var 0; loopLang$Var 1; loopLang$Var 2]))``;
val _ = print_eval "survives_mapi_assign_zero_offset"
  ``loopProps$survives 0
      (loopLang$nested_seq (MAPi
        (\i (e : 64 word loopLang$exp). loopLang$Assign (i + 0) e)
        [loopLang$Var 0; loopLang$Var 1]))``;
