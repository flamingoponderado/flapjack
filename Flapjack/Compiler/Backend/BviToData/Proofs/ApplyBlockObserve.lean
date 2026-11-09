import Flapjack.Compiler.Backend.BviToData.Proofs.State
import Flapjack.Compiler.Backend.Semantics.BviSem.Apply
import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyAux

/-! Block observation simulations for BVI-to-data correctness. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL
open Classical
noncomputable section

private theorem natBeq_eq_decide (a b : Nat) : (a == b) = decide (a = b) := by
  by_cases same : a = b
  · subst b
    simp
  · have neq : (a == b) = false := beq_eq_false_iff_ne.mpr same
    simp [neq, same]

/-- Tag tests preserve their result under timestamp erasure. This factored
case is untagged pending review of the complete primitive theorem. -/
theorem doApp_tagEq {C F : Type} (tag : Nat) (args : List DataSem.Value)
    (source : BviSem.BviState C F) (target : DataSem.State C F)
    (related : stateRel source target) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (run : BviSem.doApp (.blockOp (.tagEq tag)) (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value, DataSem.doAppAux (.blockOp (.tagEq tag)) args target = .val (value, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext := by
  cases args with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
  | cons arg rest =>
    cases rest with
    | cons a rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
    | nil =>
      cases arg <;> simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
        BvlSem.doApp, BvlSem.applyBlock, BviSem.fromBvl_toBvl] at run
      case block ts actual fields =>
        rcases run with ⟨rfl, rfl⟩
        refine ⟨target, DataSem.boolValue (decide (actual = tag)), ?_, ?_, related⟩
        · simp [DataSem.doAppAux, DataSem.applyNonFfi]
        · simp [dataToBviValue_bool, natBeq_eq_decide]

/-- Length tests preserve their result under timestamp erasure. This factored
case is untagged pending review of the complete primitive theorem. -/
theorem doApp_lenEq {C F : Type} (length : Nat) (args : List DataSem.Value)
    (source : BviSem.BviState C F) (target : DataSem.State C F)
    (related : stateRel source target) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (run : BviSem.doApp (.blockOp (.lenEq length)) (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value, DataSem.doAppAux (.blockOp (.lenEq length)) args target = .val (value, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext := by
  cases args with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
  | cons arg rest =>
    cases rest with
    | cons a rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
    | nil =>
      cases arg <;> simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
        BvlSem.doApp, BvlSem.applyBlock, BviSem.fromBvl_toBvl] at run
      case block ts tag fields =>
        rcases run with ⟨rfl, rfl⟩
        refine ⟨target, DataSem.boolValue (decide (fields.length = length)), ?_, ?_, related⟩
        · simp [DataSem.doAppAux, DataSem.applyNonFfi]
        · simp [dataToBviValue_bool, natBeq_eq_decide]

/-- Combined tag and length tests preserve their result. This factored case
is untagged pending review of the complete primitive theorem. -/
theorem doApp_tagLenEq {C F : Type} (tag length : Nat) (args : List DataSem.Value)
    (source : BviSem.BviState C F) (target : DataSem.State C F)
    (related : stateRel source target) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (run : BviSem.doApp (.blockOp (.tagLenEq tag length)) (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value, DataSem.doAppAux (.blockOp (.tagLenEq tag length)) args target = .val (value, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext := by
  cases args with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
  | cons arg rest =>
    cases rest with
    | cons a rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
    | nil =>
      cases arg <;> simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
        BvlSem.doApp, BvlSem.applyBlock, BviSem.fromBvl_toBvl] at run
      case block ts actual fields =>
        rcases run with ⟨rfl, rfl⟩
        refine ⟨target, DataSem.boolValue (decide (actual = tag ∧ fields.length = length)), ?_, ?_, related⟩
        · simp [DataSem.doAppAux, DataSem.applyNonFfi]
        · simp [dataToBviValue_bool, natBeq_eq_decide]

/-- Reading a block's length preserves its numeric result. This factored case
is untagged pending review of the complete primitive theorem. -/
theorem doApp_lengthBlock {C F : Type} (args : List DataSem.Value)
    (source : BviSem.BviState C F) (target : DataSem.State C F)
    (related : stateRel source target) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (run : BviSem.doApp (.blockOp .lengthBlock) (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value, DataSem.doAppAux (.blockOp .lengthBlock) args target = .val (value, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext := by
  cases args with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
  | cons arg rest =>
    cases rest with
    | cons a rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
    | nil =>
      cases arg <;> simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
        BvlSem.doApp, BvlSem.applyBlock, BviSem.fromBvl_toBvl] at run
      case block ts tag fields =>
        rcases run with ⟨rfl, rfl⟩
        refine ⟨target, .number fields.length, ?_, ?_, related⟩
        · simp [DataSem.doAppAux, DataSem.applyNonFfi]
        · simp [dataToBviValue]

/-- Bounds tests preserve the numeric index and block length. This factored
case is untagged pending review of the complete primitive theorem. -/
theorem doApp_boundsCheckBlock {C F : Type} (args : List DataSem.Value)
    (source : BviSem.BviState C F) (target : DataSem.State C F)
    (related : stateRel source target) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (run : BviSem.doApp (.blockOp .boundsCheckBlock) (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value, DataSem.doAppAux (.blockOp .boundsCheckBlock) args target = .val (value, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext := by
  cases args with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
  | cons arg rest =>
    cases rest with
    | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
    | cons idx rest =>
      cases rest with
      | cons extra rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
      | nil =>
        cases arg <;> simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
          BvlSem.doApp, BvlSem.applyBlock] at run
        case block ts tag fields =>
          cases idx <;> simp [dataToBviValue, BviSem.fromBvl_toBvl] at run
          case number index =>
            rcases run with ⟨rfl, rfl⟩
            refine ⟨target, DataSem.boolValue (decide (0 ≤ index ∧ index < Int.ofNat fields.length)), ?_, ?_, related⟩
            · simp [DataSem.doAppAux, DataSem.applyNonFfi]
            · simp [dataToBviValue_bool]

end
end Flapjack.Compiler.Backend.BviToData
