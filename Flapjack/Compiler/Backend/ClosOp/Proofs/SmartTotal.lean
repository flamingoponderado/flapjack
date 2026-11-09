module

public import Flapjack.Compiler.Backend.ClosOp
public import Flapjack.Compiler.Backend.ClosOp.EqBudget
public import Flapjack.Compiler.Backend.ClosLang.Proofs.Budget

@[expose] public section

/-! Executable smart-operation totality, independent of HOL correctness. -/
namespace Flapjack.Compiler.Backend.ClosOp
open ClosLang

theorem smartFuel_succeeds (fuel : Nat) (trace : BackendCommon.Tra) (op : Op) (xs : List Exp) :
    ∃ result, smartFuel fuel trace op xs = some result := by
  exact ⟨_, rfl⟩

end Flapjack.Compiler.Backend.ClosOp
