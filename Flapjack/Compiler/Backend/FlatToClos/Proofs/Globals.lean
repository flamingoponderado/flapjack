module

public import Flapjack.Misc.List
public import Flapjack.Compiler.Backend.FlatToClos.Proofs.EvaluateCases

-- Proofs below unfold private helpers of these modules.
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateFuel
import all Flapjack.Compiler.Backend.Semantics.FlatSem.Evaluate
import all Flapjack.Compiler.Backend.Semantics.FlatSem.EvaluateExact
@[expose] public section

/-! Global lookup cases for the proof-side flat-to-closure simulation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.Basis.Pure.MlString

/-- Appending equally many empty global slots preserves the state relation. -/
theorem stateRel_allocGlobals {C F : Type} (source : FlatSem.State C F) (target : ClosSem.State C F)
    (count : Nat) (states : StateRel source target) :
    StateRel { source with globals := source.globals ++ List.replicate count none }
      { target with globals := target.globals ++ List.replicate count none } := by
  rcases states with ⟨maxApp, ffi, clock, store, nonempty, slots, install⟩
  have blanks : List.Forall₂ optionalValueRel (List.replicate count none) (List.replicate count none) := by
    induction count with
    | zero => exact .nil
    | succ n ih => exact .cons trivial ih
  have appended := List.rel_append slots blanks
  refine ⟨maxApp, ffi, clock, store, ?_, ?_, install⟩
  · intro empty
    apply nonempty
    exact (List.append_eq_nil_iff.mp empty).1
  · cases globals : target.globals with
    | nil => simp [globals] at nonempty
    | cons first rest => simpa [globals] using appended

/-- Initializing corresponding empty slots preserves the global relation. -/
theorem stateRel_initGlobal {C F : Type} (source : FlatSem.State C F) (target : ClosSem.State C F)
    (index : Nat) (value : FlatSem.Value) (targetValue : ClosSem.Value)
    (states : StateRel source target) (related : ValueRel value targetValue)
    (empty : source.globals[index]? = some none) :
    ClosSem.getGlobal (index + 1) target.globals = some none ∧
    StateRel { source with globals := source.globals.set index (some value) }
      { target with globals := target.globals.set (index + 1) (some targetValue) } := by
  rcases states with ⟨maxApp, ffi, clock, store, nonempty, slots, install⟩
  obtain ⟨bound, slotEq⟩ := List.getElem?_eq_some_iff.mp empty
  have targetBound : index < target.globals.tail.length := by have := slots.length_eq; omega
  have relation := slots.get bound targetBound
  change optionalValueRel source.globals[index] target.globals.tail[index] at relation
  rw [slotEq] at relation
  have targetEq : target.globals.tail[index] = none := by
    cases found : target.globals.tail[index] <;> simp_all [optionalValueRel]
  have updated := Flapjack.forall₂_set _ _ _ (some value) (some targetValue) index ⟨related, slots⟩
  cases globals : target.globals with
  | nil => simp [globals] at nonempty
  | cons first rest =>
    simp only [globals, List.tail_cons] at targetBound targetEq updated
    have lookup : rest[index]? = some none := List.getElem?_eq_some_iff.mpr ⟨targetBound, targetEq⟩
    constructor
    · change rest[index]? = some none
      exact lookup
    · refine ⟨maxApp, ffi, clock, store, ?_, ?_, install⟩
      · simp
      · simpa [globals] using updated

/-- The target's first global is reserved, so a related source global at
index `n` appears at target index `n + 1`. -/
theorem globalLookup_related {C F : Type} (source : FlatSem.State C F) (target : ClosSem.State C F)
    (index : Nat) (value : FlatSem.Value) (states : StateRel source target)
    (found : source.globals[index]? = some (some value)) :
    ∃ targetValue, ClosSem.getGlobal (index + 1) target.globals = some (some targetValue) ∧
      ValueRel value targetValue := by
  rcases states with ⟨_, _, _, _, nonempty, slots, _⟩
  obtain ⟨bound, valueEq⟩ := List.getElem?_eq_some_iff.mp found
  have targetBound : index < target.globals.tail.length := by
    have sameLength := slots.length_eq
    omega
  have relation := slots.get bound targetBound
  change optionalValueRel source.globals[index] target.globals.tail[index] at relation
  rw [valueEq] at relation
  cases targetFound : target.globals.tail[index] with
  | none =>
    rw [targetFound] at relation
    contradiction
  | some targetValue =>
    rw [targetFound] at relation
    refine ⟨targetValue, ?_, relation⟩
    cases globals : target.globals with
    | nil => simp [globals] at nonempty
    | cons first rest =>
      simp only [globals, List.tail_cons] at targetBound targetFound
      change rest[index]? = some (some targetValue)
      exact List.getElem?_eq_some_iff.mpr ⟨targetBound, targetFound⟩

end Flapjack.Compiler.Backend.FlatToClos
