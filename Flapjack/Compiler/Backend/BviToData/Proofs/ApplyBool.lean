module

public import Flapjack.Compiler.Backend.BviToData.Proofs.State
public import Flapjack.Compiler.Backend.Semantics.BviSem.Apply
public import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyAux

@[expose] public section

/-! Boolean primitive simulation for BVI-to-data correctness. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL
open Classical
noncomputable section

/-- DATA's Boolean test agrees with projection to the BVI Boolean value. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "isBool_eq"]
theorem isBool_projection (value : DataSem.Value) (b : Bool) :
    DataSem.isBool b value ↔ BvlSem.boolValue b = dataToBviValue value := by
  cases b <;> cases value <;>
    try (simp [DataSem.isBool, BvlSem.boolValue, dataToBviValue]) <;>
    rename_i ts tag fields <;> cases fields <;>
    simp [BackendCommon.boolToTag, BackendCommon.trueTag, BackendCommon.falseTag, eq_comm]

/-- The two Boolean tags are mutually exclusive. The independent inhabited
types preserve the unused polymorphic binders in the source conjunction. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "isBool_simps"]
theorem isBool_simps {A B : Type} [Nonempty A] [Nonempty B] :
    (∀ (_ : A) (z : DataSem.Value), DataSem.isBool true z → ¬ DataSem.isBool false z) ∧
    (∀ (_ : B) (z : DataSem.Value), DataSem.isBool false z → ¬ DataSem.isBool true z) := by
  constructor <;> intro _ z <;> cases z <;>
    try (simp [DataSem.isBool]) <;>
    rename_i ts tag fields <;> cases fields <;>
    simp [BackendCommon.boolToTag, BackendCommon.trueTag, BackendCommon.falseTag] <;> omega

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

/-- A value projecting to a BVI boolean decodes to that boolean in DATA. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "data_to_bvi_v_Boolv_IMP"]
theorem dataToBvi_boolImp (value : DataSem.Value) (b : Bool)
    (h : dataToBviValue value = BvlSem.boolValue b) : DataSem.destBool value = some b := by
  rw [← destBool_projection, h]
  cases b <;> rfl

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
