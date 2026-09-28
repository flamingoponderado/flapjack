import Flapjack.Pancake.Semantics.PanSem.EvaluateClock

/-!
The `semantics_decls_has_main` theorems in `panPropsScript.sml:1611-1638`
ultimately inspect the zero-clock `Call NONE start []` evaluation.  Keep its
first source-semantic fact separate from the still-missing generic
`semantics_wrapper`/lazy-list-LUB carrier: a non-Error result from that exact
call requires a zero-argument code entry.  This helper is Flapjack-specific
proof infrastructure and has no standalone HOL declaration.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ProgHOL)
open PanSemStateFiniteExact

/-- First Call case for the HOL `semantics_decls_has_main` proof: after
    declarations have populated the code map, a non-Error result from
    `Call NONE start []` at clock zero can only come from a zero-parameter
    code entry.  HOL's `evaluate_def` performs `lookup_code` before checking
    the clock; its exact finite-support equation is
    `evaluateHOLFiniteState_call`.  This does not establish the outer
    `semantics_decls ... <> Fail` premise, whose wrapper/LUB carrier remains
    tracked separately. -/
theorem callAtZeroNonError_has_zeroArgCodeEntry
    {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (start : MlS)
    (hresult : (PanSemStateFiniteExact.evaluateHOLFiniteState { state with clock := 0 }
      (.call none start [] : ProgHOL width)).1 ≠ some .error) :
    ∃ body returnShape,
      state.code.lookup start = some ([], body, returnShape) := by
  classical
  let state0 : PanSemStateFiniteExact width σ := { state with clock := 0 }
  have hcall := evaluateHOLFiniteState_call state0 none start []
  have hargs : evalListHOLFinite state0 [] = some [] := by
    simp [evalListHOLFinite, evalListHOLExact]
  simp only [hargs] at hcall
  cases hentry : state.code.lookup start with
  | none =>
      have hentry0 : state0.code.lookup start = none := by
        simpa [state0] using hentry
      have hlookup : lookupCodeHOLFinite state0.code.lookup start [] = none := by
        apply (lookupCodeHOLFinite_eq_none_iff _ _ _).2
        simp [lookupCodeHOLExact, hentry0]
      have hrun : PanSemStateFiniteExact.evaluateHOLFiniteState state0
          (.call none start [] : ProgHOL width) = (some .error, state0) := by
        simpa [hlookup] using hcall
      exact False.elim (hresult (congrArg Prod.fst hrun))
  | some entry =>
      rcases entry with ⟨parameters, body, returnShape⟩
      have hentry0 : state0.code.lookup start =
          some (parameters, body, returnShape) := by
        simpa [state0] using hentry
      cases parameters with
      | nil =>
          exact ⟨body, returnShape, rfl⟩
      | cons parameter parameters =>
          have hlookup : lookupCodeHOLFinite state0.code.lookup start [] = none := by
            apply (lookupCodeHOLFinite_eq_none_iff _ _ _).2
            simp [lookupCodeHOLExact, hentry0]
          have hrun : PanSemStateFiniteExact.evaluateHOLFiniteState state0
              (.call none start [] : ProgHOL width) = (some .error, state0) := by
            simpa [hlookup] using hcall
          exact False.elim (hresult (congrArg Prod.fst hrun))

end Flapjack
