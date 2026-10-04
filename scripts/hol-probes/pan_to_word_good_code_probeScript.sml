(* Direct HOL-EVAL observations for the pan_to_word good-code predicates.
   The `good_panops` predicate is in pan_to_wordProofScript.sml:
     - good_panops_def (line 1108):
         good_panops (Function fi) =
           EVERY (every_exp (\x. !op es. x = Panop op es ==> LENGTH es = 2))
                 (exps_of fi.body) /\
         good_panops (Decl sh v exp) =
           every_exp (\x. !op es. x = Panop op es ==> LENGTH es = 2) exp /\
         good_panops _ = T
   Its consumer `pancake_good_code` is in pan_to_targetProofScript.sml:
     - pancake_good_code_def (line 22):
         pancake_good_code pan_code = EVERY good_panops pan_code
   Bead flapjack-cnum.

   Rows are the original definitions evaluated on concrete 64-bit
   panLang$decl values.  For declarations whose body is free of `Panop`
   (ExnDecl / Name / empty list) EVAL reduces the predicate to the Bool
   literals T.  For a `Panop` expression EVAL unfolds `good_panops` /
   `every_exp` but leaves the HOL arity predicate `\x. !op es. x = Panop op es
   ==> LENGTH es = 2` as its universally quantified normal form, because HOL's
   `EVAL` does not perform injectivity case analysis on the constructor
   equality under the `!op es` binder; the residual *is* the arity check
   (`Mul = op /\ [args] = es ==> LENGTH es = 2`).  The corresponding exact
   Lean `goodPanopsHOL` is a computable Bool and the kernel replay in
   `Flapjack.Test.PanToWordGoodCodeParity` decides those same inputs to
   true/false. *)

load "bossLib";
load "preamble";
load "panLangTheory";
load "pan_to_wordProofTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panLangTheory;
open pan_to_wordProofTheory;

fun print_eval label q =
  let val th = EVAL q
  in
    print (label ^ "=");
    print (term_to_string (rconc th));
    print "\n"
  end;

val exnDecl = ``panLang$ExnDecl «e» panLang$One : 64 panLang$decl``;
val nameDecl =
  ``panLang$Name «s» ([] : (mlstring # panLang$shape) list) : 64 panLang$decl``;
val goodDecl =
  ``panLang$Decl panLang$One «v»
      (panLang$Panop panLang$Mul [panLang$Const (1w:64 word);
                                  panLang$Const (2w:64 word)]) : 64 panLang$decl``;
val badDecl =
  ``panLang$Decl panLang$One «v»
      (panLang$Panop panLang$Mul [panLang$Const (1w:64 word)]) : 64 panLang$decl``;
val goodFun =
  ``panLang$Function
      (<| name := «f»; inline := T; export := T;
          params := ([] : (mlstring # panLang$shape) list);
          body := panLang$Return
                    (panLang$Panop panLang$Mul
                      [panLang$Const (1w:64 word); panLang$Const (2w:64 word)]);
          return := panLang$One |>) : 64 panLang$decl``;
val badFun =
  ``panLang$Function
      (<| name := «f»; inline := T; export := T;
          params := ([] : (mlstring # panLang$shape) list);
          body := panLang$Return
                    (panLang$Panop panLang$Mul [panLang$Const (1w:64 word)]);
          return := panLang$One |>) : 64 panLang$decl``;

val _ = print_eval "GoodPanopsExn" ``good_panops ^exnDecl``;
val _ = print_eval "GoodPanopsName" ``good_panops ^nameDecl``;
val _ = print_eval "GoodCodeNil"
  ``EVERY good_panops ([] : 64 panLang$decl list)``;
val _ = print_eval "GoodCodeExn" ``EVERY good_panops [^exnDecl]``;
val _ = print_eval "GoodCodeName" ``EVERY good_panops [^nameDecl]``;
val _ = print_eval "GoodPanopsDeclGood" ``good_panops ^goodDecl``;
val _ = print_eval "GoodPanopsDeclBad" ``good_panops ^badDecl``;
val _ = print_eval "GoodPanopsFunGood" ``good_panops ^goodFun``;
val _ = print_eval "GoodPanopsFunBad" ``good_panops ^badFun``;
