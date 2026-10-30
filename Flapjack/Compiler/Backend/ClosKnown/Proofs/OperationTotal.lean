import Flapjack.Compiler.Backend.ClosKnown.Proofs.MergeTotal

/-! Totality of the executable approximation operation. This is Flapjack
infrastructure and does not claim the HOL pass correctness theorem. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosLang

theorem knownOpFuel_succeeds (fuel : Nat) (op : Op) (args : List ValApprox)
    (globals : Spt ValApprox) : ∃ result, knownOpFuel fuel op args globals = some result := by
  unfold knownOpFuel
  repeat' (first | split | exact ⟨_, rfl⟩)
  case h_2 =>
    rename_i op' args' n a tail v old lookup
    obtain ⟨result, h⟩ := mergeBounded_succeeds fuel old a
    exact ⟨_, by simp [h]; rfl⟩

end Flapjack.Compiler.Backend.ClosKnown
