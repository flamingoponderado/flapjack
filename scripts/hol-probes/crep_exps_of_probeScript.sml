(* Direct HOL-EVAL probes for crepProps$exps_of.
   Reference: cakeml/pancake/semantics/crepPropsScript.sml:1282-1299.

   Regenerate the `.out` fixture with scripts/hol-probes/regenerate.sh in a
   checkout with built CakeML HOL theories:
     (cd scripts/hol-probes && ./regenerate.sh) *)
load "bossLib";
load "preamble";
load "crepPropsTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crepPropsTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "dec_seq"
  ``crepProps$exps_of
      (Dec 1 (Const (1w : 8 word))
        (Seq (Assign 2 (Var 1)) (Assign 3 (Const (2w : 8 word)))))
      : 8 crepLang$prog``;

val _ = print_eval "if_store"
  ``crepProps$exps_of
      (If (Var 3) (Store (Var 1) (Var 2)) Skip) : 8 crepLang$prog``;

val _ = print_eval "while"
  ``crepProps$exps_of (While (Const (1w : 8 word)) (Assign 2 (Var 1)))
      : 8 crepLang$prog``;

val _ = print_eval "call_tail"
  ``crepProps$exps_of
      (Call NONE (strlit "f") [Var 4; Const (6w : 8 word)]) : 8 crepLang$prog``;

val _ = print_eval "call_ret"
  ``crepProps$exps_of (Call (SOME ([], NONE)) (strlit "f") [Var 4])
      : 8 crepLang$prog``;

val _ = print_eval "call_ret_hdl"
  ``crepProps$exps_of
      (Call (SOME ([], SOME ((1w : 8 word), Assign 2 (Var 1)))) (strlit "f")
        [Var 4])
      : 8 crepLang$prog``;

val _ = print_eval "stores"
  ``(crepProps$exps_of (Store (Var 1) (Var 2)) : 8 crepLang$prog,
     crepProps$exps_of (Store32 (Var 1) (Var 2)) : 8 crepLang$prog,
     crepProps$exps_of (StoreByte (Var 1) (Var 2)) : 8 crepLang$prog,
     crepProps$exps_of (StoreGlob (1w : 5 word) (Var 7)) : 8 crepLang$prog,
     crepProps$exps_of (Return [Var 1; Const (2w : 8 word)]) : 8 crepLang$prog,
     crepProps$exps_of (Assign 9 (Var 1)) : 8 crepLang$prog,
     crepProps$exps_of (ShMem MappedRead 3 (Var 9)) : 8 crepLang$prog)``;

val _ = print_eval "empty"
  ``(crepProps$exps_of Skip : 8 crepLang$prog,
     crepProps$exps_of Tick : 8 crepLang$prog,
     crepProps$exps_of (ExtCall (strlit "g") 0 0 0 0) : 8 crepLang$prog)``;
