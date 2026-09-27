(* Direct HOL-EVAL oracle for pan_commonProps$mem_genlist_add_suc_val
   (pan_commonPropsScript.sml:234): every value of
   `GENLIST (fun x. SUC x + k) n` lies in the interval `(k, n + k]`. *)
load "bossLib";
load "preamble";
load "../semantics/pan_commonPropsTheory";
open bossLib;
open HolKernel Parse;
open preamble;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "genlist_mem_3"
  ``MEM 3 (GENLIST (\x. SUC x + 1) 4)``;
val _ = print_eval "genlist_mem_0"
  ``MEM 0 (GENLIST (\x. SUC x + 1) 4)``;
val _ = print_eval "genlist_mem_6"
  ``MEM 6 (GENLIST (\x. SUC x + 1) 4)``;
val _ = print_eval "genlist_done" ``0``;
