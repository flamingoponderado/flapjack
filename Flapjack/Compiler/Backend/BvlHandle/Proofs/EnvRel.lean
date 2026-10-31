import Flapjack.Compiler.Backend.BvlHandle.Compile
import Flapjack.Compiler.Backend.Semantics.BvlSem.State
import Flapjack.Compiler.Backend.Semantics.BvlSem.EvaluateHOL

/-! Environment agreement on the handler compiler's live variables. -/
namespace Flapjack.Compiler.Backend.BvlHandle.Proofs
open Flapjack.Compiler.Backend.DbVars
open Flapjack.Compiler.Backend.BvlSem

/-- Two environments have the same length and agree at every live index.
This indexed formulation is untagged pending review against HOL's LIST_RELi
representation. -/
def envRel (live : DbVarSet) (source target : List Value) : Prop :=
  source.length = target.length ∧
    ∀ index, index < source.length → hasVar index live = true → source[index]? = target[index]?

/-- Related environments have the same length. -/
theorem envRel_length (live : DbVarSet) (source target : List Value)
    (related : envRel live source target) : target.length = source.length := related.1.symm

/-- Every environment agrees with itself at its live indices. -/
theorem envRel_refl (live : DbVarSet) (env : List Value) : envRel live env env := by
  exact ⟨rfl, fun _ _ _ => rfl⟩

/-- Membership in a smart union is membership in either operand. -/
theorem hasVar_mkUnion (index : Nat) (left right : DbVarSet) :
    hasVar index (mkUnion left right) = (hasVar index left || hasVar index right) := by
  cases left <;> cases right <;> simp [mkUnion, hasVar]

/-- Agreement on a union of live variables is agreement on both sets. -/
theorem envRel_mkUnion (left right : DbVarSet) (source target : List Value) :
    envRel (mkUnion left right) source target ↔ envRel left source target ∧ envRel right source target := by
  simp only [envRel, hasVar_mkUnion, Bool.or_eq_true]
  constructor
  · intro ⟨length, agree⟩
    exact ⟨⟨length, fun i bound live => agree i bound (Or.inl live)⟩,
      ⟨length, fun i bound live => agree i bound (Or.inr live)⟩⟩
  · intro ⟨⟨length, leftAgree⟩, _, rightAgree⟩
    exact ⟨length, fun i bound live => live.elim (leftAgree i bound) (rightAgree i bound)⟩

/-- Replacing non-live values with zero retains exactly the agreement needed
by the handler compiler's environment relation. -/
theorem envRel_mask (live : DbVarSet) (env : List Value) :
    envRel live env (env.mapIdx fun index value =>
      if hasVar index live then value else .number 0) := by
  constructor
  · simp
  · intro index _ present
    simp [List.getElem?_mapIdx, present]

/-- Related environments return the same live value even when another
suffix is appended to the target environment. -/
theorem envRel_live_lookup (live : DbVarSet) (source target extra : List Value)
    (related : envRel live source target) (index : Nat)
    (inBounds : index < source.length) (present : hasVar index live = true) :
    (target ++ extra)[index]? = source[index]? := by
  have targetBound : index < target.length := by rw [← related.1]; exact inBounds
  simpa [List.getElem?_append, targetBound] using (related.2 index inBounds present).symm

/-- The handler compiler's variable case preserves non-type-error
evaluation under its live-variable environment relation. -/
theorem evaluate_compileSing_var {C F : Type} (limit index : Nat)
    (source target extra : List Value) (state : State C F)
    (related : envRel (compileSing limit source.length (.var index)).2.1 source target)
    (notType : (evaluate [.var index] source state).1 ≠ .err (.abort .typeError)) :
    evaluate [(compileSing limit source.length (.var index)).1] (target ++ extra) state =
      evaluate [.var index] source state := by
  by_cases inBounds : index < source.length
  · have live : hasVar index (compileSing limit source.length (.var index)).2.1 = true := by
      simp [compileSing, inBounds, hasVar]
    have lookup := envRel_live_lookup _ source target extra related index inBounds live
    simp only [compileSing, inBounds, ↓reduceIte, evaluate]
    rw [lookup]
  · cases found : source[index]? with
    | none => simp [evaluate, found] at notType
    | some value =>
      have bound := List.getElem?_eq_some_iff.mp found |>.1
      exact False.elim (inBounds bound)

/-- The force case uses the same live lookup; the thunk's recursive body
runs in its own argument environment. -/
theorem evaluate_compileSing_force {C F : Type} (limit location index : Nat)
    (source target extra : List Value) (state : State C F)
    (related : envRel (compileSing limit source.length (.force location index)).2.1 source target)
    (notType : (evaluate [.force location index] source state).1 ≠ .err (.abort .typeError)) :
    evaluate [(compileSing limit source.length (.force location index)).1] (target ++ extra) state =
      evaluate [.force location index] source state := by
  by_cases inBounds : index < source.length
  · have live : hasVar index (compileSing limit source.length (.force location index)).2.1 = true := by
      simp [compileSing, inBounds, hasVar]
    have lookup := envRel_live_lookup _ source target extra related index inBounds live
    simp only [compileSing, inBounds, ↓reduceIte, evaluate]
    rw [lookup]
  · cases found : source[index]? with
    | none => simp [evaluate, found] at notType
    | some value =>
      have bound := List.getElem?_eq_some_iff.mp found |>.1
      exact False.elim (inBounds bound)

/-- Extending both environments by identical values preserves agreement
under a corresponding de Bruijn shift. -/
theorem envRel_prepend_shift (live : DbVarSet) (source target before : List Value)
    (related : envRel (.shift before.length live) source target) :
    envRel live (before ++ source) (before ++ target) := by
  obtain ⟨length, agree⟩ := related
  constructor
  · simp [length]
  · intro index bound present
    by_cases inside : index < before.length
    · simp [List.getElem?_append, inside]
    · have sourceBound : index - before.length < source.length := by
        simp only [List.length_append] at bound
        omega
      have indexEq : index - before.length + before.length = index := by omega
      have liveShift : hasVar (index - before.length) (.shift before.length live) = true := by
        simpa [hasVar, indexEq] using present
      have same := agree (index - before.length) sourceBound liveShift
      simpa [List.getElem?_append, inside] using same

end Flapjack.Compiler.Backend.BvlHandle.Proofs
