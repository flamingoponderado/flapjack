import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileThunkAlloc

/-! FFI calls in BVL-to-BVI simulation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- Replacing the FFI state on both sides preserves the state relation. -/
theorem stateRel_setFfi {C F : Type} (relocate : Nat → Nat)
    (source : BvlSem.State (Nat × C) F) (target : BviSem.BviState C F)
    (ffi : HolFfiState F) (related : stateRel relocate source target) :
    stateRel relocate { source with ffi := ffi } { target with ffi := ffi } := by
  rcases related with ⟨refs, _, rest⟩
  exact ⟨refs, rfl, rest⟩

/-- FFI calls satisfy pass simulation given operand simulation. The normal
case preserves the same FFI state and bytes, and final FFI outcomes propagate
unchanged. Untagged pending BVI evaluator and dispatcher review. -/
theorem simulation_ffi {C F : Type} (name : Flapjack.Basis.Pure.MlString.MlString)
    (arguments : List Bvl.Exp) (env : List Value) (source : BvlSem.State (Nat × C) F)
    (argsIH : simulation arguments env source) :
    simulation [.op (.ffi name) arguments] env source := by
  cases argsRun : BvlSem.evaluate arguments env source with
  | mk argsResult middle =>
    cases argsResult with
    | err error => exact simulation_op_error (.ffi name) arguments env source middle error argsIH argsRun
    | val values =>
      intro n res next target n2 ys aux relocate run notTypeError compiled related sourceOk envOk installed handlers global
      rcases argsCompile : compileListSource n arguments with ⟨argsCode, argsAux, finalName⟩
      have nilRight : smartAppend argsAux .nil = argsAux := by cases argsAux <;> rfl
      simp [compileListSource, compileSingSource, argsCompile, nilRight, compileOp] at compiled
      rcases compiled with ⟨rfl, rfl, rfl⟩
      have shape : BvlHandle.Proofs.handleOk arguments := by simpa [BvlHandle.Proofs.handleOk] using handlers
      rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, argsRun] at run
      cases reversed : values.reverse with
      | nil =>
        simp [BvlSem.doApp, reversed] at run
        exact (notTypeError run.1.symm).elim
      | cons first tail =>
        cases tail with
        | nil =>
          simp [BvlSem.doApp, reversed] at run
          exact (notTypeError run.1.symm).elim
        | cons second rest =>
          cases rest with
          | cons third tail =>
            simp [BvlSem.doApp, reversed] at run
            exact (notTypeError run.1.symm).elim
          | nil =>
            cases first with
            | refPtr configFlag configPtr =>
              cases second with
              | refPtr flag ptr =>
                cases configLookup : middle.refs.lookup configPtr with
                | none =>
                  simp [BvlSem.doApp, reversed, configLookup] at run
                  exact (notTypeError run.1.symm).elim
                | some configCell =>
                  cases configCell with
                  | byteArray configMutable config =>
                    cases configMutable with
                    | false =>
                      simp [BvlSem.doApp, reversed, configLookup] at run
                      exact (notTypeError run.1.symm).elim
                    | true =>
                      cases bytesLookup : middle.refs.lookup ptr with
                      | none =>
                        simp [BvlSem.doApp, reversed, configLookup, bytesLookup] at run
                        exact (notTypeError run.1.symm).elim
                      | some bytesCell =>
                        cases bytesCell with
                        | byteArray mutableFlag bytes =>
                          cases mutableFlag with
                          | true =>
                            simp [BvlSem.doApp, reversed, configLookup, bytesLookup] at run
                            exact (notTypeError run.1.symm).elim
                          | false =>
                            obtain ⟨targetNext, newRelocate, clock, targetArgs, relatedNext, envEq, refsEq⟩ :=
                              argsIH n (.val values) middle target finalName argsCode argsAux relocate argsRun (by simp)
                                argsCompile related sourceOk envOk installed shape global
                            have targetConfig := stateRel_byteArray newRelocate middle targetNext true config configPtr relatedNext configLookup
                            have targetBytes := stateRel_byteArray newRelocate middle targetNext false bytes ptr relatedNext bytesLookup
                            have ffiEq : middle.ffi = targetNext.ffi := relatedNext.2.1
                            cases ffiRun : callFFIHOL middle.ffi (.extCall name) config bytes with
                            | ret ffi updated =>
                              simp [BvlSem.doApp, reversed, configLookup, bytesLookup, ffiRun] at run
                              rcases run with ⟨rfl, rfl⟩
                              have present : middle.refs.lookup ptr ≠ none := by rw [bytesLookup]; simp
                              have relatedWrite := stateRel_updateExisting newRelocate middle targetNext ptr
                                (.byteArray false updated) relatedNext present
                              have relatedFfi := stateRel_setFfi newRelocate _ _ ffi relatedWrite
                              refine ⟨{ targetNext with refs := targetNext.refs.updateEq (newRelocate ptr, .byteArray false updated), ffi := ffi },
                                newRelocate, clock, ?_, ?_, envEq, refsEq⟩
                              · rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetArgs]
                                simp only [mapSimulationResult]
                                rw [← List.map_reverse, reversed]
                                simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
                                  BviSem.toBvl, BviSem.fromBvl, adjustBv, BvlSem.unitValue, adjustValues,
                                  targetConfig, targetBytes, ← ffiEq, ffiRun]
                              · simpa [adjustRef] using relatedFfi
                            | final event =>
                              simp [BvlSem.doApp, reversed, configLookup, bytesLookup, ffiRun] at run
                              rcases run with ⟨rfl, rfl⟩
                              refine ⟨targetNext, newRelocate, clock, ?_, relatedNext, envEq, refsEq⟩
                              rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetArgs]
                              simp only [mapSimulationResult]
                              rw [← List.map_reverse, reversed]
                              simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
                                BviSem.toBvl, adjustBv, targetConfig, targetBytes, ← ffiEq, ffiRun]
                        | _ =>
                          all_goals
                            simp [BvlSem.doApp, reversed, configLookup, bytesLookup] at run
                            exact (notTypeError run.1.symm).elim
                  | _ =>
                    all_goals
                      simp [BvlSem.doApp, reversed, configLookup] at run
                      exact (notTypeError run.1.symm).elim
              | _ =>
                all_goals
                  simp [BvlSem.doApp, reversed] at run
                  exact (notTypeError run.1.symm).elim
            | _ =>
              all_goals
                cases second <;> simp [BvlSem.doApp, reversed] at run <;>
                  exact (notTypeError run.1.symm).elim

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
