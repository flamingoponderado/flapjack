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

/-- Concatenating two syntax-safe programs is safe exactly when they do not
initialize the same global. This is Flapjack infrastructure for composing
the original syntax precondition. -/
theorem syntaxOk_append_iff (xs ys : List ClosLang.Exp) :
    syntaxOk (xs ++ ys) ↔ syntaxOk xs ∧ syntaxOk ys ∧
      ∀ key, elistGlobals xs key = 0 ∨ elistGlobals ys key = 0 := by
  simp only [syntaxOk, everyFnVarsNone_append, elistGlobals_append, List.mem_append,
    or_imp, forall_and]
  constructor
  · rintro ⟨⟨annX, annY⟩, counts, freeX, freeY⟩
    refine ⟨⟨annX, ?_, freeX⟩, ⟨annY, ?_, freeY⟩, ?_⟩
    · intro key; have h := counts key; omega
    · intro key; have h := counts key; omega
    · intro key; have h := counts key; omega
  · rintro ⟨⟨annX, countX, freeX⟩, ⟨annY, countY, freeY⟩, disjoint⟩
    refine ⟨⟨annX, annY⟩, ?_, freeX, freeY⟩
    intro key
    have hx := countX key
    have hy := countY key
    have h := disjoint key
    omega

end Flapjack.Compiler.Backend.ClosKnown
