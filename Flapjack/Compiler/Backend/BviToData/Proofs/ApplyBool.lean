import Flapjack.Compiler.Backend.BviToData.Proofs.State
import Flapjack.Compiler.Backend.Semantics.BviSem.Apply
import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyAux

/-! Boolean primitive simulation for BVI-to-data correctness. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL
open Classical
noncomputable section

/-- Boolean decoding is invariant under timestamp erasure. This is Flapjack
infrastructure for primitive-application simulation. -/
theorem destBool_projection (value : DataSem.Value) :
    BvlSem.asBool (dataToBviValue value) = DataSem.destBool value := by
  cases value with
  | number n => simp [dataToBviValue, BvlSem.asBool, DataSem.destBool]
  | word64 w => simp [dataToBviValue, BvlSem.asBool, DataSem.destBool]
  | codePtr p => simp [dataToBviValue, BvlSem.asBool, DataSem.destBool]
  | refPtr b p => simp [dataToBviValue, BvlSem.asBool, DataSem.destBool]
  | block ts tag fields =>
    cases fields with
    | cons a rest => simp [dataToBviValue, BvlSem.asBool, DataSem.destBool]
    | nil =>
      cases tag with
      | zero => simp [dataToBviValue, BvlSem.asBool, DataSem.destBool]
      | succ n => cases n <;> simp [dataToBviValue, BvlSem.asBool, DataSem.destBool]

/-- Boolean negation preserves successful results and related states. This
factored case is untagged pending review of the complete primitive theorem. -/
theorem doApp_boolNot {C F : Type} (args : List DataSem.Value)
    (source : BviSem.BviState C F) (target : DataSem.State C F)
    (related : stateRel source target) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (run : BviSem.doApp (.blockOp .boolNot) (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value,
      DataSem.doAppAux (.blockOp .boolNot) args target = .val (value, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext := by
  cases args with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
  | cons arg rest =>
    cases rest with
    | cons a rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
    | nil =>
      cases decoded : DataSem.destBool arg with
      | none =>
        simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
          BvlSem.applyBlock, destBool_projection, decoded] at run
      | some b =>
        simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
          BvlSem.applyBlock, BviSem.fromBvl_toBvl, destBool_projection, decoded] at run
        rcases run with ⟨rfl, rfl⟩
        refine ⟨target, DataSem.boolValue (!b), ?_, (dataToBviValue_bool (!b)).symm, related⟩
        simp [DataSem.doAppAux, DataSem.applyNonFfi, decoded]

/-- Boolean tests preserve the decoded operands and their result. This factored
case is untagged pending review of the complete primitive theorem. -/
theorem doApp_boolTest {C F : Type} (test : AstHOL.Test) (args : List DataSem.Value)
    (source : BviSem.BviState C F) (target : DataSem.State C F)
    (related : stateRel source target) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (run : BviSem.doApp (.blockOp (.boolTest test)) (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value,
      DataSem.doAppAux (.blockOp (.boolTest test)) args target = .val (value, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext := by
  cases args with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
  | cons a rest =>
    cases rest with
    | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
    | cons b rest =>
      cases rest with
      | cons c rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
      | nil =>
        cases ha : DataSem.destBool a with
        | none =>
          simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
            BvlSem.applyBlock, destBool_projection, ha] at run
        | some x =>
          cases hb : DataSem.destBool b with
          | none =>
            simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
              BvlSem.applyBlock, destBool_projection, ha, hb] at run
          | some y =>
            simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
              BvlSem.applyBlock, BviSem.fromBvl_toBvl, destBool_projection, ha, hb] at run
            rcases run with ⟨rfl, rfl⟩
            refine ⟨target, DataSem.boolValue (x == y), ?_, (dataToBviValue_bool (x == y)).symm, related⟩
            simp [DataSem.doAppAux, DataSem.applyNonFfi, ha, hb]

end
end Flapjack.Compiler.Backend.BviToData
