import Flapjack.Compiler.Backend.Semantics.ClosProps.Globals
import Flapjack.Compiler.Backend.Semantics.ClosProps.Syntactic

/-! Source syntax precondition for known-function optimization. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open Flapjack.Compiler.Backend.ClosProps
open Flapjack.Compiler.Backend.FlatProps (emptyGlobalBag unionGlobalBag)

/-- Function annotations are absent, each global is initialized at most once,
and no closure body initializes a global. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "syntax_ok_def"]
def syntaxOk (xs : List ClosLang.Exp) : Prop :=
  everyFnVarsNone xs ∧ (∀ key, elistGlobals xs key ≤ 1) ∧ ∀ e ∈ xs, esgcFree e

/-- Flapjack helper: the original annotation predicate distributes over
concatenation. -/
theorem everyFnVarsNone_append (xs ys : List ClosLang.Exp) :
    everyFnVarsNone (xs ++ ys) ↔ everyFnVarsNone xs ∧ everyFnVarsNone ys := by
  induction xs with
  | nil => simp [everyFnVarsNone]
  | cons x xs ih => simp [everyFnVarsNone, ih, and_assoc]

/-- Flapjack helper: global initialization multiplicities add over
concatenated expression lists. -/
theorem elistGlobals_append (xs ys : List ClosLang.Exp) (key : Nat) :
    elistGlobals (xs ++ ys) key = elistGlobals xs key + elistGlobals ys key := by
  induction xs with
  | nil => simp [elistGlobals, emptyGlobalBag]
  | cons x xs ih => simp [elistGlobals, unionGlobalBag, ih, Nat.add_assoc]

end Flapjack.Compiler.Backend.ClosKnown
