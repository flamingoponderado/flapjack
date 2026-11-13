module

public import Flapjack.Compiler.Backend.BviToData.Proofs.Value
import Aesop

@[expose] public section

/-! Constructor characterizations for reference projection. -/

namespace Flapjack.Compiler.Backend.BviToData

/-- Characterize all projected reference constructors. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "data_to_bvi_ref_eq"]
theorem dataToBviRef_eq :
    (∀ (v : BvlSem.Ref DataSem.Value) (flag : Bool) (bytes : List (BitVec 8)),
      dataToBviRef v = .byteArray flag bytes ↔ v = .byteArray flag bytes) ∧
    (∀ (v : BvlSem.Ref DataSem.Value) (values : List BvlSem.Value),
      dataToBviRef v = .valueArray values ↔
        ∃ dataValues, v = .valueArray dataValues ∧ values = dataValues.map dataToBviValue) ∧
    (∀ (v : BvlSem.Ref DataSem.Value) (mode : AstHOL.ThunkMode) (value : BvlSem.Value),
      dataToBviRef v = .thunk mode value ↔
        ∃ dataValue, v = .thunk mode dataValue ∧ value = dataToBviValue dataValue) ∧
    (∀ (v : BvlSem.Ref DataSem.Value) (tag : Nat) (finished : Bool)
      (left : List BvlSem.Value) (current : BvlSem.Value) (right : List BvlSem.Value),
      dataToBviRef v = .mutBlock tag finished left current right ↔
        ∃ dataLeft dataCurrent dataRight,
          v = .mutBlock tag finished dataLeft dataCurrent dataRight ∧
          left = dataLeft.map dataToBviValue ∧ current = dataToBviValue dataCurrent ∧
          right = dataRight.map dataToBviValue) := by
  repeat' constructor
  all_goals intro v
  all_goals cases v <;> simp [dataToBviRef, eq_comm] <;> aesop

/-- The reference constructor characterizations with their equalities reversed. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "data_to_bvi_ref_eq'"]
theorem dataToBviRef_eq_flip :
    (∀ (v : BvlSem.Ref DataSem.Value) (flag : Bool) (bytes : List (BitVec 8)),
      .byteArray flag bytes = dataToBviRef v ↔ v = .byteArray flag bytes) ∧
    (∀ (v : BvlSem.Ref DataSem.Value) (values : List BvlSem.Value),
      .valueArray values = dataToBviRef v ↔
        ∃ dataValues, v = .valueArray dataValues ∧ values = dataValues.map dataToBviValue) ∧
    (∀ (v : BvlSem.Ref DataSem.Value) (mode : AstHOL.ThunkMode) (value : BvlSem.Value),
      .thunk mode value = dataToBviRef v ↔
        ∃ dataValue, v = .thunk mode dataValue ∧ value = dataToBviValue dataValue) ∧
    (∀ (v : BvlSem.Ref DataSem.Value) (tag : Nat) (finished : Bool)
      (left : List BvlSem.Value) (current : BvlSem.Value) (right : List BvlSem.Value),
      .mutBlock tag finished left current right = dataToBviRef v ↔
        ∃ dataLeft dataCurrent dataRight,
          v = .mutBlock tag finished dataLeft dataCurrent dataRight ∧
          left = dataLeft.map dataToBviValue ∧ current = dataToBviValue dataCurrent ∧
          right = dataRight.map dataToBviValue) := by
  simpa only [eq_comm] using dataToBviRef_eq

end Flapjack.Compiler.Backend.BviToData
