import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.Leaves

namespace Flapjack
open Pancake.PanLang PanSemStateFiniteExact

namespace FpermCallEntry

/-! Flapjack proof infrastructure for the entry steps in the original
`evaluate_fperm` Call proof (1746-1758). These derived transport lemmas are
untagged: they are not independently named HOL declarations, and do not claim
the recursive callee/handler constructor theorem. -/

/-- Argument evaluation is unaffected by the code permutation. -/
theorem arguments {width : Nat} {σ : Type} [NeZero width]
    (f g : MlS) (state : PanSemStateFiniteExact width σ)
    (expressions : List (ExpHOL width)) :
    evalListHOLFinite { state with code := fpermCodeHOL f g state.code }
      (h := fun address => Classical.propDecidable (state.memaddrs address)) expressions =
    evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) expressions := by
  classical
  induction expressions with
  | nil => rfl
  | cons expression rest ih =>
      simp only [evalListHOLFinite, evalListHOLExact] at ih ⊢
      rw [ih]
      have h := congrFun (@evalHOL_upd_code_eta width σ _ state
        (fun address => Classical.propDecidable (state.memaddrs address))
        (fpermCodeHOL f g state.code)) expression
      simp only [evalHOLFinite] at h
      rw [h]

/-- Canonical lookup transport, rendered at the public total evaluator's
lookup interface rather than a different raw-map evaluator. -/
theorem lookup {width : Nat} [NeZero width] (f g : MlS)
    (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name : MlS) (values : List (ValueHOL width)) :
    lookupCodeHOLFinite (fpermCodeHOL f g code).lookup (fpermName f g name) values =
      (lookupCodeHOLFinite code.lookup name values).map
        (fun entry => (fpermHOL f g entry.1, entry.2.1, entry.2.2)) :=
  lookupCodeFpermCodeHOL f g code name values

/-- Code permutation commutes with the actual decremented-clock callee entry. -/
theorem entry {width : Nat} {σ : Type} [NeZero width]
    (f g : MlS) (state : PanSemStateFiniteExact width σ)
    (callee : HolFiniteMapExact MlS (ValueHOL width)) :
    callEntryStateHOLFinite { state with code := fpermCodeHOL f g state.code } callee =
      { callEntryStateHOLFinite state callee with code := fpermCodeHOL f g state.code } := rfl

/-- Every nonrecursive Call entry outcome is transported, including missing
arguments, missing code, and zero clock. The disjunction identifies only these
entry cases; this infrastructure is not the full HOL constructor theorem. -/
theorem nonrecursive {width : Nat} {σ : Type} [NeZero width]
    (f g : MlS) (state : PanSemStateFiniteExact width σ)
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (name : MlS) (expressions : List (ExpHOL width))
    (hentry : evalListHOLFinite state
        (h := fun address => Classical.propDecidable (state.memaddrs address)) expressions = none ∨
      (∃ values, evalListHOLFinite state
          (h := fun address => Classical.propDecidable (state.memaddrs address)) expressions = some values ∧
        (lookupCodeHOLFinite state.code.lookup name values = none ∨ state.clock = 0))) :
    evaluateHOLFiniteState { state with code := fpermCodeHOL f g state.code }
        (fpermHOL f g (.call info name expressions)) =
      let result := evaluateHOLFiniteState state (.call info name expressions)
      (result.1, { result.2 with code := fpermCodeHOL f g result.2.code }) := by
  classical
  have hperm : fpermHOL f g (.call info name expressions) =
      .call (match info with
        | none => none
        | some (destination, handler) => some (destination, match handler with
          | none => none
          | some (eid, binding, program) => some (eid, binding, fpermHOL f g program)))
        (fpermName f g name) expressions := by
    cases info with
    | none => simp only [fpermHOL]
    | some pair =>
      obtain ⟨destination, handler⟩ := pair
      cases handler with
      | none => simp only [fpermHOL]
      | some triple =>
        obtain ⟨eid, binding, program⟩ := triple
        simp only [fpermHOL]
  rw [hperm]
  simp only [evaluateHOLFiniteState_call]
  rw [arguments f g state expressions]
  rcases hentry with hargs | ⟨values, hargs, hlookup | hclock⟩
  · simp only [hargs]
  · simp only [hargs]
    rw [lookup f g state.code name values, hlookup]
    rfl
  · simp only [hargs]
    rw [lookup f g state.code name values]
    cases hl : lookupCodeHOLFinite state.code.lookup name values with
    | none => rfl
    | some result =>
        obtain ⟨body, callee, shape⟩ := result
        simp only [Option.map_some, hclock, if_true]
        simp only [emptyLocalsHOLFinite, hclock]

end FpermCallEntry
end Flapjack
