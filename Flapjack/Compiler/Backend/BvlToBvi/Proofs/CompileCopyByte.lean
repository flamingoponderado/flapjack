import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileElemAt

/-! In-place byte-array copying in BVL-to-BVI simulation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)
open Flapjack.SemanticPrimitivesHOL (copyArray)

/-- A successful in-place byte copy has precisely the source operand and heap
shape. -/
theorem copyByte_shape {C F : Type} (args : List Value) (source next : BvlSem.State C F)
    (value : Value) (run : BvlSem.applyMemory (.copyByte false) args source = some (value, next)) :
    ∃ sf src off len df dst dstOff sourceFlag sourceBytes destFlag destBytes copied,
      args = [.refPtr sf src, .number off, .number len, .refPtr df dst, .number dstOff] ∧
      source.refs.lookup src = some (.byteArray sourceFlag sourceBytes) ∧
      source.refs.lookup dst = some (.byteArray destFlag destBytes) ∧
      copyArray (sourceBytes, off) len (some (destBytes, dstOff)) = some copied ∧
      value = BvlSem.unitValue ∧ next = { source with refs := source.refs.updateEq (dst, .byteArray destFlag copied) } := by
  unfold BvlSem.applyMemory at run
  repeat' first | split at run | contradiction
  all_goals simp_all [Option.bind_eq_some_iff]
  all_goals obtain ⟨srcCell, srcLookup, remainder⟩ := run
  all_goals cases srcCell <;> simp_all [Option.bind_eq_some_iff]
  all_goals obtain ⟨destCell, destLookup, result⟩ := remainder
  all_goals cases destCell <;> simp_all [Option.bind_eq_some_iff]
  all_goals aesop (add safe cases Bool)

/-- An in-place byte copy updates the corresponding target cell. Untagged
pending BVI dispatcher correspondence review. -/
theorem doCopyByte_target {C F : Type} (relocate : Nat → Nat)
    (source : BvlSem.State (Nat × C) F) (target : BviSem.BviState C F)
    (sf : Bool) (src : Nat) (off len : Int) (df : Bool) (dst : Nat) (dstOff : Int)
    (sourceFlag : Bool) (sourceBytes : List (BitVec 8)) (destFlag : Bool) (destBytes copied : List (BitVec 8))
    (related : stateRel relocate source target)
    (srcLookup : source.refs.lookup src = some (.byteArray sourceFlag sourceBytes))
    (dstLookup : source.refs.lookup dst = some (.byteArray destFlag destBytes))
    (copy : copyArray (sourceBytes, off) len (some (destBytes, dstOff)) = some copied) :
    BviSem.doApp (.memOp (.copyByte false))
      ([.refPtr sf src, .number off, .number len, .refPtr df dst, .number dstOff].map (adjustBv relocate)) target =
      .val (adjustBv relocate BvlSem.unitValue,
        { target with refs := target.refs.updateEq (relocate dst, .byteArray destFlag copied) }) := by
  have targetSrc := stateRel_byteArray relocate source target sourceFlag sourceBytes src related srcLookup
  have targetDst := stateRel_byteArray relocate source target destFlag destBytes dst related dstLookup
  simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory,
    BviSem.toBvl, BviSem.fromBvl, adjustBv, BvlSem.unitValue, adjustValues, targetSrc, targetDst, copy]

/-- In-place byte copying satisfies pass simulation given operand simulation.
Untagged pending BVI evaluator and dispatcher correspondence review. -/
theorem simulation_copyByte {C F : Type} (arguments : List Bvl.Exp)
    (env : List Value) (source : BvlSem.State (Nat × C) F)
    (argsIH : simulation arguments env source) :
    simulation [.op (.memOp (.copyByte false)) arguments] env source := by
  cases argsRun : BvlSem.evaluate arguments env source with
  | mk argsResult middle =>
    cases argsResult with
    | err error => exact simulation_op_error (.memOp (.copyByte false)) arguments env source middle error argsIH argsRun
    | val values =>
      intro n res next target n2 ys aux relocate run notTypeError compiled related sourceOk envOk installed handlers global
      rcases argsCompile : compileListSource n arguments with ⟨argsCode, argsAux, finalName⟩
      have nilRight : smartAppend argsAux .nil = argsAux := by cases argsAux <;> rfl
      simp [compileListSource, compileSingSource, argsCompile, nilRight, compileOp] at compiled
      rcases compiled with ⟨rfl, rfl, rfl⟩
      have shape : BvlHandle.Proofs.handleOk arguments := by simpa [BvlHandle.Proofs.handleOk] using handlers
      rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, argsRun] at run
      cases application : BvlSem.applyMemory (.copyByte false) values.reverse middle with
      | none =>
        simp [BvlSem.doApp, application] at run
        exact (notTypeError run.1.symm).elim
      | some pair =>
        rcases pair with ⟨result, last⟩
        obtain ⟨sf, src, off, len, df, dst, dstOff, sourceFlag, sourceBytes, destFlag, destBytes, copied,
          argsEq, srcLookup, dstLookup, copy, rfl, rfl⟩ := copyByte_shape values.reverse middle last result application
        simp [BvlSem.doApp, application] at run
        rcases run with ⟨rfl, rfl⟩
        obtain ⟨targetNext, newRelocate, clock, targetArgs, relatedNext, envEq, refsEq⟩ :=
          argsIH n (.val values) middle target finalName argsCode argsAux relocate argsRun (by simp)
            argsCompile related sourceOk envOk installed shape global
        have present : middle.refs.lookup dst ≠ none := by rw [dstLookup]; simp
        have relatedWrite := stateRel_updateExisting newRelocate middle targetNext dst (.byteArray destFlag copied) relatedNext present
        refine ⟨{ targetNext with refs := targetNext.refs.updateEq (newRelocate dst, .byteArray destFlag copied) },
          newRelocate, clock, ?_, ?_, envEq, refsEq⟩
        · rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetArgs]
          simp only [mapSimulationResult]
          rw [← List.map_reverse, argsEq,
            doCopyByte_target newRelocate middle targetNext sf src off len df dst dstOff
              sourceFlag sourceBytes destFlag destBytes copied relatedNext srcLookup dstLookup copy]
          simp
        · simpa [adjustRef] using relatedWrite

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
