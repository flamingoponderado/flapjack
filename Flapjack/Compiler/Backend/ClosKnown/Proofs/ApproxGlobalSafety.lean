import Flapjack.Compiler.Backend.ClosKnown.Merge
import Flapjack.Compiler.Backend.Semantics.ClosProps.Globals
import Flapjack.Misc.Sptree

/-! Global-write safety of known-function approximations. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosProps
open FlatProps (emptyGlobalBag)

/-- Inlined bodies in an approximation do not write globals. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "val_approx_sgc_free_def" 248]
def valApproxSgcFree : ValApprox → Prop
  | .clos _ _ body _ => setGlobals body = emptyGlobalBag
  | .tuple _ values => ∀ value ∈ values, valApproxSgcFree value
  | _ => True
termination_by a => sizeOf a
decreasing_by all_goals have := List.sizeOf_lt_of_mem ‹_›; simp_wf; omega

/-- All stored global approximations satisfy the closure-body invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "globals_approx_sgc_free_def"]
def globalsApproxSgcFree (g : Spt ValApprox) : Prop :=
  ∀ n a, sptLookup n g = some a → valApproxSgcFree a

/-- Pairwise merge preserves a property when it holds for each paired input. -/
private theorem mergeListSafe (xs ys : List ValApprox)
    (step : ∀ x ∈ xs, ∀ y ∈ ys, valApproxSgcFree (mergeHOL x y)) :
    ∀ z ∈ mergeListHOL xs ys, valApproxSgcFree z := by
  induction xs generalizing ys with
  | nil => simp [mergeListHOL]
  | cons x xs ih =>
    cases ys with
    | nil => simp [mergeListHOL]
    | cons y ys =>
      simp only [mergeListHOL, List.mem_cons, forall_eq_or_imp]
      constructor
      · exact step x (by simp) y (by simp)
      · exact ih ys (fun a ha b hb => step a (by simp [ha]) b (by simp [hb]))

/-- Merging two safe approximations preserves closure-body safety. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "val_approx_sgc_free_merge"]
theorem valApproxSgcFreeMerge (a b : ValApprox)
    (safe : valApproxSgcFree a ∧ valApproxSgcFree b) : valApproxSgcFree (mergeHOL a b) := by
  have all : ∀ n (a b : ValApprox), sizeOf a < n →
      valApproxSgcFree a → valApproxSgcFree b → valApproxSgcFree (mergeHOL a b) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro a b bound ha hb
      cases a <;> cases b <;> simp_all [mergeHOL, valApproxSgcFree]
      all_goals split <;> simp_all [valApproxSgcFree]
      apply mergeListSafe
      intro x hx y hy
      have smaller := List.sizeOf_lt_of_mem hx
      have xbound : sizeOf x + 1 < n := by omega
      exact ih (sizeOf x + 1) xbound x y (by omega) (ha x hx) (hb y hy)
  exact all (sizeOf a + 1) a b (by omega) safe.1 safe.2

end Flapjack.Compiler.Backend.ClosKnown
