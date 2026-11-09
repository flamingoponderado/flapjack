module

public import Flapjack.Compiler.Backend.BviToData.Proofs.Value
public import Flapjack.Compiler.Backend.Semantics.DataSem.Int
public import Flapjack.Compiler.Backend.Semantics.BvlSem.Int

@[expose] public section

/-! Integer operations under the BVI-to-data value projection. -/
namespace Flapjack.Compiler.Backend.BviToData

/-- Every successful data integer operation agrees with the corresponding
BVI operation after erasing timestamps. Data's small-constant restriction is
preserved as a premise through successful evaluation. -/
theorem doIntApp_projection (op : ClosLang.IntOp) (args : List DataSem.Value) (result : DataSem.Value)
    (run : DataSem.doIntApp op args = some result) :
    BvlSem.doIntApp op (args.map dataToBviValue) = some (dataToBviValue result) := by
  cases op <;> cases args with
  | nil =>
    simp_all [DataSem.doIntApp, BvlSem.doIntApp] <;>
      rcases run with ⟨_, rfl⟩ <;> simp [dataToBviValue]
  | cons a rest =>
    cases rest with
    | nil =>
      cases a <;> simp_all [DataSem.doIntApp, BvlSem.doIntApp, dataToBviValue,
        DataSem.boolValue, BvlSem.boolValue] <;>
        rcases run with ⟨_, rfl⟩ <;> simp [dataToBviValue]
    | cons b rest =>
      cases rest with
      | nil =>
        cases a <;> cases b <;> simp_all [DataSem.doIntApp, BvlSem.doIntApp, dataToBviValue,
          DataSem.boolValue, BvlSem.boolValue] <;>
          first | (rcases run with ⟨_, rfl⟩; simp [dataToBviValue]) | (subst result; simp [dataToBviValue])
      | cons c rest => simp_all [DataSem.doIntApp]

/-- All non-constant integer operations commute with timestamp erasure,
including their failure cases. Constants are handled separately by the BVI
dispatcher, which enforces the data language's small-integer bound. This is
Flapjack pass-simulation infrastructure. -/
theorem doIntApp_projection_nonconst (op : ClosLang.IntOp) (args : List DataSem.Value)
    (notConst : ∀ n, op ≠ .const n) :
    (DataSem.doIntApp op args).map dataToBviValue =
      BvlSem.doIntApp op (args.map dataToBviValue) := by
  cases op <;> cases args with
  | nil => simp_all [DataSem.doIntApp, BvlSem.doIntApp]
  | cons a rest =>
    cases rest with
    | nil =>
      cases a <;> simp_all [DataSem.doIntApp, BvlSem.doIntApp, dataToBviValue,
        DataSem.boolValue, BvlSem.boolValue]
    | cons b rest =>
      cases rest with
      | nil =>
        cases a <;> cases b <;> simp_all [DataSem.doIntApp, BvlSem.doIntApp, dataToBviValue,
          DataSem.boolValue, BvlSem.boolValue]
        all_goals split <;> simp_all [dataToBviValue]
      | cons c rest => simp_all [DataSem.doIntApp, BvlSem.doIntApp]

end Flapjack.Compiler.Backend.BviToData
