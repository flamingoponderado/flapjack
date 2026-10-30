import Flapjack.Compiler.Backend.ClosOp.Proofs.EqMeasure
import Flapjack.Compiler.Backend.ClosOp.Proofs.LiftTotal

/-! Executable smart-operation totality, independent of HOL correctness. -/
namespace Flapjack.Compiler.Backend.ClosOp
open ClosLang

theorem smartFuel_succeeds (fuel : Nat) (trace : BackendCommon.Tra) (op : Op) (xs : List Exp) :
    ∃ result, smartFuel fuel trace op xs = some result := by
  unfold smartFuel
  repeat' (first | split | exact ⟨_, rfl⟩)
  case h_2 =>
      rename_i unused x y a b h op' hv d hd
      obtain ⟨⟨lifted, n, binds⟩, hl⟩ := liftBounded_succeeds fuel [x, y] 0 []
      simp only [hl]
      cases lifted with
      | nil => exact ⟨_, rfl⟩
      | cons a tail =>
        cases tail with
        | nil => exact ⟨_, rfl⟩
        | cons b tail =>
          cases tail with
          | nil =>
            obtain ⟨result, he⟩ := eqListBounded_succeeds fuel [(a, b)]
            exact ⟨_, by simp [he]; rfl⟩
          | cons c tail => exact ⟨_, rfl⟩

end Flapjack.Compiler.Backend.ClosOp
