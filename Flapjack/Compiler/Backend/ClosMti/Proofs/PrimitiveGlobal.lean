import Flapjack.Compiler.Backend.ClosMti.Proofs.EvaluatePrimitive

/-! Global primitive operations for multi-argument introduction. -/
namespace Flapjack.Compiler.Backend.ClosMti
open Flapjack ClosSem SemanticPrimitivesProps

/-- Replacing corresponding positions in related lists preserves their relation. -/
theorem forall₂_set {A B : Type} {rel : A → B → Prop} {left : List A} {right : List B}
    (related : List.Forall₂ rel left right) (index : Nat) (value : A) (nextValue : B)
    (valueRel : rel value nextValue) :
    List.Forall₂ rel (left.set index value) (right.set index nextValue) := by
  induction related generalizing index with
  | nil => simp
  | cons head tail ih =>
    cases index with
    | zero => exact .cons valueRel tail
    | succ index => exact .cons head (ih index)

/-- Corresponding global lookups preserve missing and uninitialized slots. -/
theorem stateRel_getGlobal {C F : Type} {source target : State C F}
    (related : StateRel source target) (index : Nat) :
    optionRel (ValueRel source.maxApp) (getGlobal index source.globals).join
      (getGlobal index target.globals).join := by
  have globals := related.2.2.2.2.2.2.2.1
  have lookup := forall₂_getElemRel globals index
  cases left : getGlobal index source.globals with
  | none =>
    cases right : getGlobal index target.globals <;> simp_all [getGlobal, optionRel]
  | some leftSlot =>
    cases right : getGlobal index target.globals with
    | none => simp_all [getGlobal, optionRel]
    | some rightSlot =>
      cases leftSlot <;> cases rightSlot <;> simp_all [getGlobal, optionRel, ValueRelOpt]

/-- Appending equal numbers of empty globals preserves related states. -/
theorem stateRel_allocGlobals {C F : Type} {source target : State C F}
    (count : Nat) (related : StateRel source target) :
    StateRel { source with globals := source.globals ++ List.replicate count none }
      { target with globals := target.globals ++ List.replicate count none } := by
  have blanks : List.Forall₂ (ValueRelOpt source.maxApp)
      (List.replicate count none) (List.replicate count none) := by
    induction count with
    | zero => exact .nil
    | succ n ih => exact .cons trivial ih
  exact stateRel_withGlobals related _ _ (forall₂_append_lists related.2.2.2.2.2.2.2.1 blanks)

/-- Global reads preserve missing slots and relate initialized values. -/
theorem primitiveSimulation_global_read {C F : Type} (index : Nat) :
    @PrimitiveSimulation C F (.globOp (.global index)) := by
  intro source target left right states values
  cases values with
  | nil =>
    have lookup := stateRel_getGlobal states index
    cases l : (getGlobal index source.globals).join <;>
      cases r : (getGlobal index target.globals).join <;>
      simp_all [optionRel, doApp, applyGlobal, excRel]
  | cons head tail =>
    cases tail with
    | nil =>
      cases head with
      | number number =>
        by_cases negative : number < 0
        · simp [doApp, applyGlobal, negative, excRel]
        · have lookup := stateRel_getGlobal states number.toNat
          cases l : (getGlobal number.toNat source.globals).join <;>
            cases r : (getGlobal number.toNat target.globals).join <;>
            simp_all [optionRel, doApp, applyGlobal, excRel]
          simp [show ¬ number < 0 by omega, lookup, states]
      | word64 _ | block _ _ _ _ | byteVector _ | refPtr _ _ | closure | recclosure | partialRecclosure =>
        simp [doApp, applyGlobal, excRel]
    | cons head tail =>
      cases head <;> simp [doApp, applyGlobal, excRel]

/-- Global allocation appends corresponding empty slots. -/
theorem primitiveSimulation_global_alloc {C F : Type} :
    @PrimitiveSimulation C F (.globOp .allocGlobal) := by
  intro source target left right states values
  cases values with
  | nil => simp [doApp, applyGlobal, excRel]
  | cons head tail =>
    cases tail with
    | nil =>
      cases head with
      | number number =>
        by_cases negative : number < 0
        · simp [doApp, applyGlobal, negative, excRel]
        · have appended := stateRel_allocGlobals number.toNat states
          have unitRel : ValueRel source.maxApp unitValue unitValue := .block _ [] [] .nil
          simp [doApp, applyGlobal, negative, unitRel, appended]
      | word64 _ | block _ _ _ _ | byteVector _ | refPtr _ _ | closure | recclosure | partialRecclosure =>
        simp [doApp, applyGlobal, excRel]
    | cons head tail => cases head <;> simp [doApp, applyGlobal, excRel]

/-- Initializing a global preserves related stores and rejects nonempty or
out-of-range slots on both sides. -/
theorem primitiveSimulation_global_set {C F : Type} (index : Nat) :
    @PrimitiveSimulation C F (.globOp (.setGlobal index)) := by
  intro source target left right states values
  cases values with
  | nil => simp [doApp, applyGlobal, excRel]
  | cons head tail =>
    cases tail with
    | nil =>
      rename_i value nextValue
      have globals := states.2.2.2.2.2.2.2.1
      have slots := forall₂_getElemRel globals index
      have updated : StateRel { source with globals := source.globals.set index (some value) }
          { target with globals := target.globals.set index (some nextValue) } :=
        stateRel_withGlobals states _ _ (forall₂_set globals index _ _ head)
      have unitRel : ValueRel source.maxApp unitValue unitValue := .block _ [] [] .nil
      cases l : getGlobal index source.globals with
      | none => cases r : getGlobal index target.globals <;>
          simp_all [getGlobal, optionRel, ValueRelOpt, doApp, applyGlobal, excRel]
      | some leftValue =>
        cases r : getGlobal index target.globals with
        | none => simp_all [getGlobal, optionRel]
        | some rightValue =>
          cases leftValue <;> cases rightValue <;>
            simp_all [getGlobal, optionRel, ValueRelOpt, doApp, applyGlobal, excRel]
    | cons head tail => simp [doApp, applyGlobal, excRel]

/-- All global operations satisfy the primitive simulation. -/
theorem primitiveSimulation_global {C F : Type} (op : ClosLang.GlobOp) :
    @PrimitiveSimulation C F (.globOp op) := by
  cases op with
  | global index => exact primitiveSimulation_global_read index
  | setGlobal index => exact primitiveSimulation_global_set index
  | allocGlobal => exact primitiveSimulation_global_alloc
  | globalsPtr | setGlobalsPtr =>
    intro source target left right states values
    simp [doApp, applyGlobal, excRel]

end Flapjack.Compiler.Backend.ClosMti
