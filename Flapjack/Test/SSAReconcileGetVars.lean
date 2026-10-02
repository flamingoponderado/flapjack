import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAReconcileGetVars

/-! Native reconciliation reads allow aliased SSA destinations and do not
require lookup success in the SSA tree itself. Flapjack-specific kernel
regressions, no additional HOL declarations. -/
namespace Flapjack.Test.SSAReconcileGetVars
open Flapjack Flapjack.Compiler.Backend.WordAlloc

-- Distinct source names may refer to the same target local. This catches an
-- accidental injectivity premise in the full theorem's interface.
example {width : Nat} [NeZero width] {C F : Type}
    (state : WordSemStateFiniteExact width C F) (value : WordLocW width)
    (present : sptLookup 1 state.locals = some value) :
    ∃ vs, WordSemStateFiniteExact.getVars [1, 1] state = some vs ∧
      vs.length = 2 ∧ ∀ i, i < 2 → sptLookup 1 state.locals = some (holEl i vs) := by
  let ssa : Spt Nat := sptInsert 7 1 (sptInsert 9 1 .ln)
  have h7 : sptLookup 7 ssa = some 1 := sptLookup_sptInsert_same _ _ _
  have h9 : sptLookup 9 ssa = some 1 := by
    simp [ssa, sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
  obtain ⟨vs, read, length, indexed⟩ := ssaReconcileGetVarsLemma [7, 9] ssa state
    ⟨by decide, by
      intro v member
      simp at member
      rcases member with rfl | rfl
      · exact ⟨value, by simpa [h7, holThe] using present⟩
      · exact ⟨value, by simpa [h9, holThe] using present⟩⟩
  refine ⟨vs, by simpa [h7, h9, holThe] using read, length, ?_⟩
  intro i bound
  have h := indexed i bound
  have cases : i = 0 ∨ i = 1 := by omega
  rcases cases with rfl | rfl
  · simpa [holEl, holHd, h7, holThe] using h
  · simpa [holEl, holHd, h9, holThe] using h

-- The original THE allows a missing SSA lookup, provided the resulting
-- unspecified target local is present. No extra domain premise is introduced.
example {width : Nat} [NeZero width] {C F : Type}
    (state : WordSemStateFiniteExact width C F) (value : WordLocW width)
    (present : sptLookup (holThe (none : Option Nat)) state.locals = some value) :
    ∃ vs, WordSemStateFiniteExact.getVars [holThe (none : Option Nat)] state = some vs ∧
      vs.length = 1 ∧ sptLookup (holThe (none : Option Nat)) state.locals =
        some (holEl 0 vs) := by
  obtain ⟨vs, read, length, indexed⟩ := ssaReconcileGetVarsLemma [7] (.ln : Spt Nat) state
    ⟨by decide, by
      intro v member
      simp only [List.mem_singleton] at member
      subst v
      exact ⟨value, present⟩⟩
  exact ⟨vs, read, length, indexed 0 (by decide)⟩

#print axioms ssaReconcileGetVarsLemma
end Flapjack.Test.SSAReconcileGetVars
