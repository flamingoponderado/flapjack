import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
import Flapjack.Pancake.Semantics.PanSem.Semantics

/-!
The `semantics_decls_has_main` theorems in `panPropsScript.sml:1611-1638`
ultimately inspect the zero-clock `Call NONE start []` evaluation.  Keep its
first source-semantic fact separate: a non-Error result from that exact
call requires a zero-argument code entry. The second helper derives that
result premise from the exact semantics' non-failure test. These helpers are
Flapjack-specific proof infrastructure and have no standalone HOL declaration.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ProgHOL)
open PanSemStateFiniteExact

/-- First Call case for the HOL `semantics_decls_has_main` proof: after
    declarations have populated the code map, a non-Error result from
    `Call NONE start []` at clock zero can only come from a zero-parameter
    code entry.  HOL's `evaluate_def` performs `lookup_code` before checking
    the clock; its exact finite-support equation is
    `evaluateHOLFiniteState_call`. This helper alone does not establish the
    outer `semantics_decls ... <> Fail` premise or the declaration code update. -/
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

/-- Flapjack-specific infrastructure for the zero-clock step in the proofs
    of `semantics_decls_has_main` and its prime variant (HOL lines 1611–1638).
    There is no separate HOL declaration for this intermediate result.
    The only premise is non-failure of the reviewed exact semantics; the
    non-Error evaluator fact is derived from its failure test internally. -/
theorem semanticsNonFail_has_zeroArgCodeEntry
    {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (start : MlS)
    (hsem : semantics state start ≠ .fail) :
    ∃ body returnShape,
      state.code.lookup start = some ([], body, returnShape) := by
  classical
  apply callAtZeroNonError_has_zeroArgCodeEntry state start
  intro herror
  apply hsem
  unfold semantics
  dsimp only
  rw [if_pos]
  exact ⟨0, by rw [herror]; trivial⟩

end Flapjack
