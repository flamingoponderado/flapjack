module

public import Flapjack.Compiler.Backend.ClosMti.Proofs.EvaluatePrimitive

@[expose] public section

/-! Reference allocation for multi-argument introduction. -/
namespace Flapjack.Compiler.Backend.ClosMti
open Flapjack ClosSem SemanticPrimitivesProps

/-- Related stores agree on whether an address is free. -/
theorem stateRel_ref_unused {C F : Type} {source target : State C F}
    (related : StateRel source target) (index : Nat) :
    source.refs.lookup index = none ↔ target.refs.lookup index = none := by
  have lookup := stateRel_lookupRefs related index
  cases left : source.refs.lookup index <;> cases right : target.refs.lookup index <;>
    simp_all [optionRel]

/-- Related stores choose the same least unused reference. -/
theorem stateRel_leastUnusedRef {C F : Type} {source target : State C F}
    (related : StateRel source target) : leastUnusedRef source.refs = leastUnusedRef target.refs := by
  apply Nat.le_antisymm
  · by_contra notLe
    have smaller : leastUnusedRef target.refs < leastUnusedRef source.refs := by omega
    have occupied := leastUnusedRef_minimal source.refs _ smaller
    have free := (stateRel_ref_unused related _).mpr (leastUnusedRef_unused target.refs)
    exact occupied free
  · by_contra notLe
    have smaller : leastUnusedRef source.refs < leastUnusedRef target.refs := by omega
    have occupied := leastUnusedRef_minimal target.refs _ smaller
    have free := (stateRel_ref_unused related _).mp (leastUnusedRef_unused source.refs)
    exact occupied free

/-- Allocating a reference preserves its address and relates its stored values. -/
theorem primitiveSimulation_memory_ref {C F : Type} :
    @PrimitiveSimulation C F (.memOp .ref) := by
  intro source target left right states values
  have addressEq := stateRel_leastUnusedRef states
  have updated := stateRel_updateRefs states (leastUnusedRef source.refs)
    (.valueArray left) (.valueArray right) (.valueArray left right values)
  have pointerRel : ValueRel source.maxApp (.refPtr true (leastUnusedRef source.refs))
      (.refPtr true (leastUnusedRef source.refs)) := .refPtr _ _
  simp [doApp, applyMemory, ← addressEq, pointerRel, updated]

/-- Replicated array allocation preserves related initial values and rejects
negative sizes on both sides. -/
theorem primitiveSimulation_memory_refArray {C F : Type} :
    @PrimitiveSimulation C F (.memOp .refArray) := by
  intro source target left right states values
  cases values with
  | nil => simp [doApp, applyMemory, excRel]
  | cons first tail =>
    cases tail with
    | nil => simp [doApp, applyMemory, excRel]
    | cons second tail =>
      cases tail with
      | nil =>
        cases first with
        | number count =>
          rename_i value nextValue
          by_cases negative : count < 0
          · simp [doApp, applyMemory, negative, excRel]
          · have repeated : List.Forall₂ (ValueRel source.maxApp)
                (List.replicate count.toNat value) (List.replicate count.toNat nextValue) := by
              generalize count.toNat = n
              induction n with
              | zero => exact .nil
              | succ n ih => exact .cons second ih
            have addressEq := stateRel_leastUnusedRef states
            have updated := stateRel_updateRefs states (leastUnusedRef source.refs)
              (.valueArray (List.replicate count.toNat value))
              (.valueArray (List.replicate count.toNat nextValue))
              (.valueArray _ _ repeated)
            have pointerRel : ValueRel source.maxApp (.refPtr true (leastUnusedRef source.refs))
                (.refPtr true (leastUnusedRef source.refs)) := .refPtr _ _
            simp [doApp, applyMemory, negative, ← addressEq, pointerRel, updated]
        | word64 _ | block _ _ _ _ | byteVector _ | refPtr _ _ | closure | recclosure | partialRecclosure =>
          simp [doApp, applyMemory, excRel]
      | cons head tail => simp [doApp, applyMemory, excRel]

/-- Byte-array allocation preserves byte conversion, size checks and the
resulting related stores. -/
theorem primitiveSimulation_memory_refByte {C F : Type} :
    @PrimitiveSimulation C F (.memOp (.refByte false)) := by
  intro source target left right states values
  cases values with
  | nil => simp [doApp, applyMemory, excRel]
  | cons first tail =>
    cases tail with
    | nil => simp [doApp, applyMemory, excRel]
    | cons second tail =>
      cases tail with
      | nil =>
        cases first with
        | number count =>
          cases second with
          | number byte =>
            by_cases negative : count < 0
            · simp [doApp, applyMemory, negative, excRel]
            · cases converted : intToByte byte with
              | none => simp [doApp, applyMemory, negative, converted, excRel]
              | some value =>
                have addressEq := stateRel_leastUnusedRef states
                have updated := stateRel_updateRefs states (leastUnusedRef source.refs)
                  (.byteArray (List.replicate count.toNat value))
                  (.byteArray (List.replicate count.toNat value)) (.byteArray _)
                have pointerRel : ValueRel source.maxApp (.refPtr true (leastUnusedRef source.refs))
                    (.refPtr true (leastUnusedRef source.refs)) := .refPtr _ _
                simp [doApp, applyMemory, negative, converted, ← addressEq, pointerRel, updated]
          | word64 _ | block _ _ _ _ | byteVector _ | refPtr _ _ | closure | recclosure | partialRecclosure =>
            simp [doApp, applyMemory, excRel]
        | word64 _ | block _ _ _ _ | byteVector _ | refPtr _ _ | closure | recclosure | partialRecclosure =>
          cases second <;> simp [doApp, applyMemory, excRel]
      | cons head tail => simp [doApp, applyMemory, excRel]

end Flapjack.Compiler.Backend.ClosMti
