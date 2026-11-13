module

public import Flapjack.CakeParser.PtreeConversion
public import Flapjack.CakeParser.Grammar
public import Flapjack.Misc.Grammar
public import Flapjack.Misc.List
public import Flapjack.AstHOL.Syntax
public import Flapjack.Basis.Pure.MlString
public import Flapjack.NamespaceHOL

@[expose] public section

/-! Exact generic ports of `cakeml/semantics/cmlPtreeConversionScript.sml`'s
parse-tree conversion helpers, stated over the reviewed generic grammar
carrier `Flapjack.Misc.Grammar.ParseTree` so HOL's polymorphic terminal,
nonterminal and location types are preserved. The executed conversion keeps
its specialized `Flapjack.CakeParser.ParseTree` implementation; the two are
connected by `Flapjack.CakeParser.ParseTree.toGrammarTree` and
`ofGrammarTree`. -/
namespace Flapjack.CakeParser.PtreeConversion.Exact

open Flapjack.Basis.Pure.MlString Flapjack.NamespaceHOL

/-- Exact port of HOL `ifM_def` (`cmlPtreeConversionScript.sml:96`): the
    option-monadic conditional, selecting the first branch on `SOME T` and the
    second on every other boolean option. -/
@[hol "cakeml/semantics/cmlPtreeConversionScript.sml" "ifM_def"]
def ifMHOL {α : Type} (bM : Option Bool) (tM eM : Option α) : Option α :=
  bM >>= fun b => if b then tM else eM

/-- Exact port of HOL `isSymbolicConstructor`
    (`cmlPtreeConversionScript.sml:533`): the character list spells `"::"`. -/
@[hol "cakeml/semantics/cmlPtreeConversionScript.sml" "isSymbolicConstructor_def"]
def isSymbolicConstructorHOL (s : List HolChar) : Option Bool :=
  some (s = [58, 58])

/-- Exact port of HOL `isConstructor` (`cmlPtreeConversionScript.sml:538`):
    symbolic constructors plus a character list whose head is an uppercase
    alphabetic character. -/
@[hol "cakeml/semantics/cmlPtreeConversionScript.sml" "isConstructor_def"]
def isConstructorHOL (s : List HolChar) : Option Bool :=
  ifMHOL (isSymbolicConstructorHOL s) (some true)
    (some (match Flapjack.oHD s with
      | none => false
      | some c => isAlphaChar c && isUpperChar c))

/-- Exact port of HOL `tokcheck_def`, generic in the terminal type `α`, the
    nonterminal type `β` and the location type `γ`. HOL's equality on the
    generic terminal type is rendered by `DecidableEq α`, the established
    rendering of HOL equality on a generic key type. -/
@[hol "cakeml/semantics/cmlPtreeConversionScript.sml" "tokcheck_def"]
def tokcheckHOL {α β γ : Type} [DecidableEq α]
    (pt : Misc.Grammar.ParseTree α β γ) (tok : α) : Bool :=
  decide ((Misc.Grammar.destLf pt >>= Misc.Grammar.destTokSym) = some tok)

/-- Exact port of HOL `tokcheckl_def`: pointwise `tokcheck` over the tree and
    token lists, false when the lists have different lengths. -/
@[hol "cakeml/semantics/cmlPtreeConversionScript.sml" "tokcheckl_def"]
def tokchecklHOL {α β γ : Type} [DecidableEq α] :
    List (Misc.Grammar.ParseTree α β γ) → List α → Bool
  | [], [] => true
  | pt :: prest, tok :: tokrest => tokcheckHOL pt tok && tokchecklHOL prest tokrest
  | _, _ => false

/-- Exact port of HOL `singleSymP_def`: the single-leaf symbol token of a
    one-element tree list, filtered by `P` and returned as `Short`. Generic in
    the identifier's module type `α`, the nonterminal type `β` and the location
    type `γ`, with the terminal type fixed to CakeML's `token`. HOL's
    `assert (P s)` guard is the `if P s` test around `return (Short s)`. -/
@[hol "cakeml/semantics/cmlPtreeConversionScript.sml" "singleSymP_def"]
def singleSymPHOL {α β γ : Type} (P : Basis.Pure.MlString.MlString → Bool) :
    List (Misc.Grammar.ParseTree CakeParser.Token β γ) →
      Option (Ident α Basis.Pure.MlString.MlString)
  | [pt] =>
      (Misc.Grammar.destLf pt >>= Misc.Grammar.destTokSym >>= CakeParser.destSymbolT) >>= fun s =>
        if P s then some (.short s) else none
  | _ => none

end Flapjack.CakeParser.PtreeConversion.Exact
