import Flapjack.Compiler.Backend.ClosCall.Proofs.ValueRelation
import Flapjack.Compiler.Backend.Semantics.ClosProps.RefRelations
import Flapjack.Compiler.Backend.Semantics.ClosProps.SimpleRelations
import Flapjack.Compiler.Backend.ClosMti.Proofs.StateRelation

/-! Fuel-aware closure-state relation for direct-call conversion. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem ClosProps

/-- States related by direct-call conversion: observable state agrees,
globals and references contain related values, and the source code map is
empty. The source compiler configuration retains the known-location set.
This is untagged because its value relation uses bounded direct-call
traversals rather than HOL's total `calls`. -/
def StateRelFuel {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F) : Prop :=
  source.ffi = target.ffi ∧ source.clock = target.clock ∧ source.maxApp = target.maxApp ∧
    List.Forall₂ (optionRel (ValueRelFuel fuel g allowed target.code)) source.globals target.globals ∧
    ClosMti.fmapRel (refRel (ValueRelFuel fuel g allowed target.code)) source.refs target.refs ∧
    source.code = HolFiniteMapExact.empty

private theorem optionRel_mono {A B : Type} {R S : A → B → Prop} {x : Option A} {y : Option B}
    (change : ∀ a b, R a b → S a b) (related : optionRel R x y) : optionRel S x y := by
  cases x <;> cases y <;> simp_all [optionRel]

/-- Extending the compiler state and permitted locations preserves the
fuel-aware state relation for the same source and target states. -/
theorem stateRelFuel_mono {C F : Type} {fuel : Nat} {g g' : State}
    {allowed allowed' : Set Nat} {source : ClosSem.State (NumSet × C) F} {target : ClosSem.State C F}
    (related : StateRelFuel fuel g allowed source target)
    (stateGrowth : stateExtends g g') (allowedGrowth : allowed ⊆ allowed') :
    StateRelFuel fuel g' allowed' source target := by
  obtain ⟨ffi, clock, maxApp, globals, refs, sourceCode⟩ := related
  have growValue : ∀ a b, ValueRelFuel fuel g allowed target.code a b →
      ValueRelFuel fuel g' allowed' target.code a b := by
    intro a b values
    exact valueRelFuel_mono values stateGrowth allowedGrowth (fun _ _ h => h)
  refine ⟨ffi, clock, maxApp, ?_, ?_, sourceCode⟩
  · exact List.Forall₂.imp (fun _ _ h => optionRel_mono growValue h) globals
  · refine ⟨refs.1, ?_⟩
    intro key value lookup
    obtain ⟨value', found, values⟩ := refs.2 key value lookup
    exact ⟨value', found, refRel_mono growValue values⟩

/-- Looking up a reference in related states yields related optional values. -/
theorem stateRelFuel_lookupRefs {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {source : ClosSem.State (NumSet × C) F} {target : ClosSem.State C F}
    (related : StateRelFuel fuel g allowed source target) (key : Nat) :
    Flapjack.optionRel (refRel (ValueRelFuel fuel g allowed target.code))
      (source.refs.lookup key) (target.refs.lookup key) :=
  ClosMti.fmapRel_lookup related.2.2.2.2.1 key

/-- Updating both reference stores with related references preserves the
fuel-aware state relation. -/
theorem stateRelFuel_updateRefs {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {source : ClosSem.State (NumSet × C) F} {target : ClosSem.State C F}
    (related : StateRelFuel fuel g allowed source target) (key : Nat)
    (left right : ClosSem.Ref ClosSem.Value)
    (values : refRel (ValueRelFuel fuel g allowed target.code) left right) :
    StateRelFuel fuel g allowed { source with refs := source.refs.updateEq (key, left) }
      { target with refs := target.refs.updateEq (key, right) } := by
  obtain ⟨ffi, clock, maxApp, globals, refs, sourceCode⟩ := related
  exact ⟨ffi, clock, maxApp, globals, ClosMti.fmapRel_update refs key left right values, sourceCode⟩

/-- Fixing the target code map makes the fuel-aware state relation satisfy
the generic primitive-operation simulation interface. -/
theorem stateRelFuel_simple {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) :
    simpleStateRel (ValueRelFuel fuel g allowed code)
      (fun (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F) =>
        target.code = code ∧ StateRelFuel fuel g allowed source target) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s t ptr ⟨missing, codeEq, states⟩
    have lookup := stateRelFuel_lookupRefs states ptr
    cases left : s.refs.lookup ptr <;> simp_all [Flapjack.optionRel]
  · intro bytes t s ptr ⟨found, codeEq, states⟩
    have lookup := stateRelFuel_lookupRefs states ptr
    rw [found] at lookup
    cases left : s.refs.lookup ptr with
    | none => simp [Flapjack.optionRel, left] at lookup
    | some value =>
      have refs : refRel (ValueRelFuel fuel g allowed code) value (.byteArray bytes) := by
        simpa [Flapjack.optionRel, left, codeEq] using lookup
      cases value <;> simp_all [refRel]
  · intro values t s ptr ⟨found, codeEq, states⟩
    have lookup := stateRelFuel_lookupRefs states ptr
    rw [found] at lookup
    cases left : s.refs.lookup ptr with
    | none => simp [Flapjack.optionRel, left] at lookup
    | some value =>
      have refs : refRel (ValueRelFuel fuel g allowed code) value (.valueArray values) := by
        simpa [Flapjack.optionRel, left, codeEq] using lookup
      cases value with
      | valueArray xs => exact ⟨xs, rfl, refs⟩
      | byteArray bytes => exact refs.elim
      | thunk mode v => exact refs.elim
  · intro mode value t s ptr ⟨found, codeEq, states⟩
    have lookup := stateRelFuel_lookupRefs states ptr
    rw [found] at lookup
    cases left : s.refs.lookup ptr with
    | none => simp [Flapjack.optionRel, left] at lookup
    | some old =>
      have refs : refRel (ValueRelFuel fuel g allowed code) old (.thunk mode value) := by
        simpa [Flapjack.optionRel, left, codeEq] using lookup
      cases old with
      | valueArray xs => exact refs.elim
      | byteArray bytes => exact refs.elim
      | thunk mode' v =>
        obtain ⟨rfl, valueRel⟩ := refs
        exact ⟨v, rfl, valueRel⟩
  · intro s t ⟨codeEq, states⟩
    exact ⟨states.1, states.2.2.2.2.1.1, by simpa [codeEq] using states.2.2.2.1⟩
  · intro ffi s t ⟨codeEq, states⟩
    obtain ⟨_, clock, maxApp, globals, refs, sourceCode⟩ := states
    exact ⟨codeEq, rfl, clock, maxApp, globals, refs, sourceCode⟩
  · intro bytes s t ptr ⟨codeEq, states⟩
    exact ⟨codeEq, stateRelFuel_updateRefs states ptr _ _ rfl⟩
  · intro s t ptr xs ys ⟨⟨codeEq, states⟩, values⟩
    refine ⟨codeEq, stateRelFuel_updateRefs states ptr _ _ ?_⟩
    simpa [refRel, codeEq] using values
  · intro s t ptr mode v w ⟨⟨codeEq, states⟩, values⟩
    refine ⟨codeEq, stateRelFuel_updateRefs states ptr _ _ ?_⟩
    simpa [refRel, codeEq] using values
  · intro s t xs ys ⟨⟨codeEq, states⟩, values⟩
    obtain ⟨ffi, clock, maxApp, _, refs, sourceCode⟩ := states
    refine ⟨codeEq, ffi, clock, maxApp, ?_, refs, sourceCode⟩
    simpa [codeEq] using values

end Flapjack.Compiler.Backend.ClosCall
