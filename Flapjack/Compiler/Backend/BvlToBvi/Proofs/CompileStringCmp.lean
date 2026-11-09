import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileXorByte

/-! Byte-string comparison in BVL-to-BVI simulation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)
open Flapjack.SemanticPrimitivesHOL (strCmp)
open Flapjack.Basis.Pure.MlString (MlString)

/-- A successful string comparison reads two byte arrays and preserves state. -/
theorem stringCmp_shape {C F : Type} (fast : Bool) (op : Opb) (args : List Value)
    (source next : BvlSem.State C F) (value : Value)
    (run : BvlSem.applyMemory (.stringCmp fast op) args source = some (value, next)) :
    ∃ lf left rf right leftFlag leftBytes rightFlag rightBytes,
      args = [.refPtr lf left, .refPtr rf right] ∧
      source.refs.lookup left = some (.byteArray leftFlag leftBytes) ∧
      source.refs.lookup right = some (.byteArray rightFlag rightBytes) ∧
      value = BvlSem.boolValue (strCmp fast op (MlString.implode leftBytes) (MlString.implode rightBytes)) ∧
      next = source := by
  unfold BvlSem.applyMemory at run
  repeat' first | split at run | contradiction
  all_goals simp_all [Option.bind_eq_some_iff]
  all_goals obtain ⟨leftCell, leftLookup, remainder⟩ := run
  all_goals cases leftCell <;> simp_all [Option.bind_eq_some_iff]
  all_goals obtain ⟨rightCell, rightLookup, result⟩ := remainder
  all_goals cases rightCell <;> simp_all

/-- String comparison sees the same byte arrays after relocation. Untagged
pending BVI dispatcher correspondence review. -/
theorem doStringCmp_target {C F : Type} (fast : Bool) (op : Opb) (relocate : Nat → Nat)
    (source : BvlSem.State (Nat × C) F) (target : BviSem.BviState C F)
    (lf : Bool) (left : Nat) (rf : Bool) (right : Nat)
    (leftFlag : Bool) (leftBytes : List (BitVec 8)) (rightFlag : Bool) (rightBytes : List (BitVec 8))
    (related : stateRel relocate source target)
    (leftLookup : source.refs.lookup left = some (.byteArray leftFlag leftBytes))
    (rightLookup : source.refs.lookup right = some (.byteArray rightFlag rightBytes)) :
    BviSem.doApp (.memOp (.stringCmp fast op))
      ([.refPtr lf left, .refPtr rf right].map (adjustBv relocate)) target =
      .val (adjustBv relocate (BvlSem.boolValue
        (strCmp fast op (MlString.implode leftBytes) (MlString.implode rightBytes))), target) := by
  have targetLeft := stateRel_byteArray relocate source target leftFlag leftBytes left related leftLookup
  have targetRight := stateRel_byteArray relocate source target rightFlag rightBytes right related rightLookup
  simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory,
    BviSem.toBvl, BviSem.fromBvl, adjustBv, adjustBv_bool, targetLeft, targetRight]

/-- String comparison satisfies pass simulation given operand simulation.
Untagged pending BVI evaluator and dispatcher correspondence review. -/
theorem simulation_stringCmp {C F : Type} (fast : Bool) (op : Opb) (arguments : List Bvl.Exp)
    (env : List Value) (source : BvlSem.State (Nat × C) F)
    (argsIH : simulation arguments env source) :
    simulation [.op (.memOp (.stringCmp fast op)) arguments] env source := by
  cases argsRun : BvlSem.evaluate arguments env source with
  | mk argsResult middle =>
    cases argsResult with
    | err error => exact simulation_op_error (.memOp (.stringCmp fast op)) arguments env source middle error argsIH argsRun
    | val values =>
      intro n res next target n2 ys aux relocate run notTypeError compiled related sourceOk envOk installed handlers global
      rcases argsCompile : compileListSource n arguments with ⟨argsCode, argsAux, finalName⟩
      have nilRight : smartAppend argsAux .nil = argsAux := by cases argsAux <;> rfl
      simp [compileListSource, compileSingSource, argsCompile, nilRight, compileOp] at compiled
      rcases compiled with ⟨rfl, rfl, rfl⟩
      have shape : BvlHandle.Proofs.handleOk arguments := by simpa [BvlHandle.Proofs.handleOk] using handlers
      rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, argsRun] at run
      cases application : BvlSem.applyMemory (.stringCmp fast op) values.reverse middle with
      | none =>
        simp [BvlSem.doApp, application] at run
        exact (notTypeError run.1.symm).elim
      | some pair =>
        rcases pair with ⟨result, last⟩
        obtain ⟨lf, left, rf, right, leftFlag, leftBytes, rightFlag, rightBytes,
          argsEq, leftLookup, rightLookup, resultEq, lastEq⟩ := stringCmp_shape fast op values.reverse middle last result application
        subst result
        subst last
        simp [BvlSem.doApp, application] at run
        rcases run with ⟨rfl, rfl⟩
        obtain ⟨targetNext, newRelocate, clock, targetArgs, relatedNext, envEq, refsEq⟩ :=
          argsIH n (.val values) middle target finalName argsCode argsAux relocate argsRun (by simp)
            argsCompile related sourceOk envOk installed shape global
        refine ⟨targetNext, newRelocate, clock, ?_, relatedNext, envEq, refsEq⟩
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetArgs]
        simp only [mapSimulationResult]
        rw [← List.map_reverse, argsEq,
          doStringCmp_target fast op newRelocate middle targetNext lf left rf right
            leftFlag leftBytes rightFlag rightBytes relatedNext leftLookup rightLookup]
        simp

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
