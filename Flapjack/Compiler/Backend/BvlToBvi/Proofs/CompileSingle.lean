import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileCorrect

/-! Entry-point simulation for BVL-to-BVI compilation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)
open Flapjack.SemanticPrimitivesHOL (Result)

/-- Calling the compiled entry point simulates the corresponding BVL call.
The result remains untagged pending BVI evaluator and dispatcher review. -/
theorem compileSingleEvaluate {C F : Type} (start : Nat)
    (source next : BvlSem.State (Nat × C) F) (target : BviSem.BviState C F)
    (res : Result (List Value) Value) (relocate : Nat → Nat)
    (run : BvlSem.evaluate [.call 0 (some start) []] [] source = (res, next))
    (related : stateRel relocate source target) (global : target.global.isSome = true)
    (sourceOk : stateOk source) (notTypeError : res ≠ .err (.abort .typeError)) :
    ∃ clock newRelocate targetNext,
      BviSem.evaluate [.call 0 (some (bvlNumStubs + bvlToBviNamespaces * start)) [] none] []
          (BviProps.incClock clock target) = (mapSimulationResult newRelocate res, targetNext) ∧
      stateRel newRelocate next targetNext := by
  have compiled : compileListSource 0 [.call 0 (some start) []] =
      ([.call 0 (some (bvlNumStubs + bvlToBviNamespaces * start)) [] none], .nil, 0) := by
    simp [compileListSource, compileSingSource, smartAppend]
  obtain ⟨targetNext, newRelocate, clock, targetRun, finalRel, _, _⟩ :=
    compileExpsCorrect [.call 0 (some start) []] [] source next 0 0 res target
      [.call 0 (some (bvlNumStubs + bvlToBviNamespaces * start)) [] none] .nil relocate run notTypeError
      compiled related sourceOk (by simp [bvOkList]) (by simp [appListAppend, appendAux, auxCodeInstalled])
      (by simp [BvlHandle.Proofs.handleOk]) global
  exact ⟨clock, newRelocate, targetNext, by simpa using targetRun, finalRel⟩

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
