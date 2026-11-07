import Flapjack.CakeParser.Grammar
import Flapjack.Misc.Location

/-! First-order token predicates used by the executable CakeML PEG. -/
namespace Flapjack.CakeParser.PegChecks
open Flapjack.Basis.Pure.MlString Flapjack.Misc.Location Grammar

@[hol "cakeml/compiler/parsing/pegexec_cml_foScript.sml" "token_alpha_check"]
inductive AlphaCheck where
  | nonempty | upperInitial | lowerInitialNotReserved
  deriving DecidableEq, Repr

@[hol "cakeml/compiler/parsing/pegexec_cml_foScript.sml" "token_symbol_check"]
inductive SymbolCheck where
  | nonempty | validMult | validAdd | validRel | validList | validPrefix
  deriving DecidableEq, Repr

@[hol "cakeml/compiler/parsing/pegexec_cml_foScript.sml" "token_longid_check"]
inductive LongidCheck where
  | tailNonempty | tailNonemptyHeadAlphaNotUpper | ctorUpperInitial
  deriving DecidableEq, Repr

@[hol "cakeml/compiler/parsing/pegexec_cml_foScript.sml" "token_check"]
inductive TokenCheck where
  | always | never | eq : Token → TokenCheck
  | isInt | isString | isChar | isWord | isFfi
  | alpha : AlphaCheck → TokenCheck
  | symbol : SymbolCheck → TokenCheck
  | longid : LongidCheck → TokenCheck
  | isTyvar | isAlphaSym | isLongid | opidLongidNonempty | opidSymbolNonempty | opidAlphaNonempty
  deriving DecidableEq, Repr

private def upper (c : HolChar) : Bool := 65 ≤ c.toNat && c.toNat ≤ 90
private def alpha (c : HolChar) : Bool := upper c || (97 ≤ c.toNat && c.toNat ≤ 122)

/-- Evaluate the source alpha-identifier predicate. -/
@[hol "cakeml/compiler/parsing/pegexec_cml_foScript.sml" "eval_token_alpha_check_def"]
def evalAlpha (check : AlphaCheck) (s : MlString) : Bool :=
  match check, s.explode with
  | .nonempty, xs => !xs.isEmpty
  | .upperInitial, c :: _ => upper c
  | .lowerInitialNotReserved, c :: _ =>
      !upper c && s != ofString "before" && s != ofString "div" && s != ofString "mod" && s != ofString "o"
  | _, [] => false

/-- Evaluate the source symbolic-operator predicate. -/
@[hol "cakeml/compiler/parsing/pegexec_cml_foScript.sml" "eval_token_symbol_check_def"]
def evalSymbol (check : SymbolCheck) (s : MlString) : Bool :=
  match check with
  | .nonempty => !s.explode.isEmpty
  | .validMult => validMultSym s.explode
  | .validAdd => validAddSym s.explode
  | .validRel => validRelSym s.explode
  | .validList => validListSym s.explode
  | .validPrefix => validPrefixSym s.explode

/-- Evaluate the source predicate on a qualified identifier's tail. -/
@[hol "cakeml/compiler/parsing/pegexec_cml_foScript.sml" "eval_token_longid_check_alt_def"]
def evalLongid (check : LongidCheck) (name : Path × MlString) : Bool :=
  match check, name.2.explode with
  | _, [] => false
  | .tailNonempty, _ :: _ => true
  | .tailNonemptyHeadAlphaNotUpper, c :: _ => !alpha c || !upper c
  | .ctorUpperInitial, c :: _ => alpha c && upper c

/-- Evaluate a first-order PEG token predicate, ignoring its location. -/
@[hol "cakeml/compiler/parsing/pegexec_cml_foScript.sml" "eval_token_check_def"]
def evalToken (check : TokenCheck) (input : Token × Locs) : Bool :=
  let t := input.1
  match check, t with
  | .always, _ => true
  | .never, _ => false
  | .eq a, b => decide (a = b)
  | .isInt, .intT _ | .isString, .stringT _ | .isChar, .charT _ | .isWord, .wordT _ | .isFfi, .ffiT _ => true
  | .alpha p, .alphaT s => evalAlpha p s
  | .symbol p, .symbolT s => evalSymbol p s
  | .longid p, .longidT path s => evalLongid p (path, s)
  | .isTyvar, .tyvarT _ | .isAlphaSym, .alphaT _ | .isAlphaSym, .symbolT _ | .isLongid, .longidT _ _ => true
  | .opidLongidNonempty, .longidT _ s | .opidSymbolNonempty, .symbolT s | .opidAlphaNonempty, .alphaT s => !s.explode.isEmpty
  | _, _ => false

end Flapjack.CakeParser.PegChecks
