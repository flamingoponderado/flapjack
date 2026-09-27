(* Direct original Pancake HOL EVAL rows for the structural clauses of
   crep_inline$inline_prog_def (cakeml/pancake/crep_inlineScript.sml:239-248).
   With FEMPTY and no Call nodes to inline, the recursive structural clauses
   preserve each exact Crep program shape. *)

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

val dec = ``(Dec 1 (Const (1w:8 word)) Skip) : 8 crepLang$prog``;
val seq = ``(Seq ^dec Skip) : 8 crepLang$prog``;
val ite = ``(If (Const (1w:8 word)) ^dec Skip) : 8 crepLang$prog``;
val whl = ``(While (Const (0w:8 word)) ^seq) : 8 crepLang$prog``;

val _ = print_eval "inline_prog_empty_dec" ``inline_prog FEMPTY ^dec = ^dec``;
val _ = print_eval "inline_prog_empty_seq" ``inline_prog FEMPTY ^seq = ^seq``;
val _ = print_eval "inline_prog_empty_if" ``inline_prog FEMPTY ^ite = ^ite``;
val _ = print_eval "inline_prog_empty_while" ``inline_prog FEMPTY ^whl = ^whl``;
