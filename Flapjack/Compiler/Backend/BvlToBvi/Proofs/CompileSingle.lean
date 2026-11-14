module

public import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileCorrect

@[expose] public section

/-! Entry-point simulation for BVL-to-BVI compilation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)
open Flapjack.SemanticPrimitivesHOL (Result)

namespace CompileSingleCarrier
/-- Canonical BVL reference-map state roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_State {C F : Type} :
    (∀ s : BvlSem.StateBroad C F, (BvlSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : BvlSem.State C F, BvlSem.State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness

/-- Canonical BVI reference-map state roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_BviState {C F : Type} :
    (∀ s : BviSem.BviStateBroad C F, (BviSem.BviState.ofBroad s).toBroad = s) ∧
      (∀ s : BviSem.BviState C F, BviSem.BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness
end CompileSingleCarrier

/-- Calling the compiled entry point simulates the corresponding BVL call.
This follows from the complete expression compilation simulation. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "compile_single_evaluate"
  (fmap_as_finite_support_relation := [State.refs, BviState.refs])]
theorem compileSingleEvaluate {C F : Type} (start : Nat)
    (source next : BvlSem.State (Nat × C) F) (target : BviSem.BviState C F)
    (res : Result (List Value) Value) (relocate : Nat → Nat)
    (premises : BvlSem.evaluate [.call 0 (some start) []] [] source = (res, next) ∧
      stateRel relocate source target ∧ target.global.isSome = true ∧ stateOk source ∧
      res ≠ .err (.abort .typeError)) :
    ∃ clock newRelocate targetNext,
      BviSem.evaluate [.call 0 (some (bvlNumStubs + bvlToBviNamespaces * start)) [] none] []
          (BviProps.incClock clock target) =
        (Flapjack.SemanticPrimitivesProps.mapResult (List.map (adjustBv newRelocate))
          (fun value => BviSem.ExnOrRet.exn (adjustBv newRelocate value)) res, targetNext) ∧
      stateRel newRelocate next targetNext := by
  obtain ⟨run, related, global, sourceOk, notTypeError⟩ := premises
  have compiled : compileListSource 0 [.call 0 (some start) []] =
      ([.call 0 (some (bvlNumStubs + bvlToBviNamespaces * start)) [] none], .nil, 0) := by
    simp [compileListSource, compileSingSource, smartAppend]
  obtain ⟨targetNext, newRelocate, clock, targetRun, finalRel, _, _⟩ :=
    compileExpsCorrect [.call 0 (some start) []] [] source 0 res next target 0
      [.call 0 (some (bvlNumStubs + bvlToBviNamespaces * start)) [] none] .nil relocate
      ⟨run, notTypeError, compiled, related, sourceOk, by simp [bvOkList],
        by simp [appListAppend, appendAux, auxCodeInstalled], by simp [BvlHandle.Proofs.handleOk], global⟩
  exact ⟨clock, newRelocate, targetNext, by simpa only [List.map_nil] using targetRun, finalRel⟩

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
