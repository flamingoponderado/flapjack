import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.ForeignCalls
import Flapjack.Misc.RichList

/-! Reference allocation under the closure-annotation state relation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps

/-- Related reference maps have the same allocated domain. -/
theorem stateRel_ref_unused {C F : Type} (source target : State C F) (states : StateRel source target)
    (index : Nat) : source.refs.lookup index = none ↔ target.refs.lookup index = none := by
  have related := states.2.2.2.2.2.2.1 index
  cases left : source.refs.lookup index <;> cases right : target.refs.lookup index <;>
    simp [left, right, optionRel] at related ⊢

/-- Equal reference domains give the same least fresh address. -/
theorem stateRel_leastUnusedRef {C F : Type} (source target : State C F) (states : StateRel source target) :
    leastUnusedRef source.refs = leastUnusedRef target.refs := by
  have sourceFree := leastUnusedRef_unused source.refs
  have targetFree := leastUnusedRef_unused target.refs
  have sourceLe : leastUnusedRef source.refs ≤ leastUnusedRef target.refs := by
    by_contra notLe
    have smaller : leastUnusedRef target.refs < leastUnusedRef source.refs := by omega
    have occupied := leastUnusedRef_minimal source.refs _ smaller
    exact occupied ((stateRel_ref_unused source target states _).mpr targetFree)
  have targetLe : leastUnusedRef target.refs ≤ leastUnusedRef source.refs := by
    by_contra notLe
    have smaller : leastUnusedRef source.refs < leastUnusedRef target.refs := by omega
    have occupied := leastUnusedRef_minimal target.refs _ smaller
    exact occupied ((stateRel_ref_unused source target states _).mp sourceFree)
  omega

/-- Allocating an array of related values picks the same fresh address and
preserves the state relation. -/
theorem primitiveSimulation_ref {C F : Type} :
    PrimitiveSimulation (C := C) (F := F) (.memOp .ref) := by
  intro values nextValues source target valuesRel states
  let index := leastUnusedRef source.refs
  have fresh : leastUnusedRef target.refs = index := (stateRel_leastUnusedRef source target states).symm
  have nextStates := stateRel_updateRefFfi source target states index (.valueArray values)
    (.valueArray nextValues) valuesRel source.ffi
  refine ⟨.val (.refPtr true index, { target with refs := target.refs.updateEq (index, .valueArray nextValues) }), ?_, ?_⟩
  · simp [doApp, applyMemory, fresh, index]
  · simp only [doApp, applyMemory, AppResultRel]
    refine ⟨.refPtr true index, ?_⟩
    simpa [index, states.2.1] using nextStates

/-- Array allocation picks the same address and initializes related values. -/
theorem primitiveSimulation_refArray {C F : Type} :
    PrimitiveSimulation (C := C) (F := F) (.memOp .refArray) := by
  intro values nextValues source target valuesRel states
  cases valuesRel with
  | nil =>
    exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
  | cons countRel rest =>
    cases rest with
    | nil =>
      exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
    | cons valueRel rest =>
      cases rest with
      | nil =>
        cases countRel with
        | number count =>
          by_cases negative : count < 0
          · exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory, negative], by
              simp [doApp, applyMemory, negative, AppResultRel, ResultRel]⟩
          · rename_i value nextValue
            let index := leastUnusedRef source.refs
            have fresh : leastUnusedRef target.refs = index := (stateRel_leastUnusedRef source target states).symm
            have arrays := (forall₂_replicate_iff ValueRel count.toNat value nextValue).mpr (fun _ => valueRel)
            have nextStates := stateRel_updateRefFfi source target states index
              (.valueArray (List.replicate count.toNat value))
              (.valueArray (List.replicate count.toNat nextValue)) arrays source.ffi
            refine ⟨.val (.refPtr true index,
              { target with refs := target.refs.updateEq (index, .valueArray (List.replicate count.toNat nextValue)) }), ?_, ?_⟩
            · simp [doApp, applyMemory, negative, fresh, index]
            · simp only [doApp, applyMemory, if_neg negative, AppResultRel]
              refine ⟨.refPtr true index, ?_⟩
              simpa [index, states.2.1] using nextStates
        | _ =>
          exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
      | cons third rest =>
        exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩

/-- Byte-array allocation has matching validation and preserves byte contents. -/
theorem primitiveSimulation_refByte {C F : Type} (flag : Bool) :
    PrimitiveSimulation (C := C) (F := F) (.memOp (.refByte flag)) := by
  intro values nextValues source target valuesRel states
  cases flag with
  | true =>
    exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
  | false =>
    cases valuesRel with
    | nil =>
      exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
    | cons countRel rest =>
      cases rest with
      | nil =>
        exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
      | cons byteRel rest =>
        cases rest with
        | nil =>
          cases countRel with
          | number count =>
            cases byteRel with
            | number byte =>
              by_cases negative : count < 0
              · exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory, negative], by
                  simp [doApp, applyMemory, negative, AppResultRel, ResultRel]⟩
              · cases decoded : intToByte byte with
                | none =>
                  exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory, negative, decoded], by
                    simp [doApp, applyMemory, negative, decoded, AppResultRel, ResultRel]⟩
                | some b =>
                  let index := leastUnusedRef source.refs
                  let bytes := List.replicate count.toNat b
                  have fresh : leastUnusedRef target.refs = index := (stateRel_leastUnusedRef source target states).symm
                  have nextStates := stateRel_updateRefFfi source target states index
                    (.byteArray bytes) (.byteArray bytes) rfl source.ffi
                  refine ⟨.val (.refPtr true index,
                    { target with refs := target.refs.updateEq (index, .byteArray bytes) }), ?_, ?_⟩
                  · simp [doApp, applyMemory, negative, decoded, fresh, index, bytes]
                  · simp only [doApp, applyMemory, if_neg negative, decoded, AppResultRel]
                    refine ⟨.refPtr true index, ?_⟩
                    simpa [index, bytes, states.2.1] using nextStates
            | _ =>
              exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
          | _ => cases byteRel <;>
              exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
        | cons third rest =>
          exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩

end Flapjack.Compiler.Backend.ClosAnnotate
