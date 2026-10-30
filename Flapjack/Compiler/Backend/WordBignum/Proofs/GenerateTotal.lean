import Flapjack.Compiler.Backend.WordBignum.Generate
import Flapjack.Compiler.Backend.WordBignum.Proofs.CompileTotal

/-! Totality of the captured-mini-program generator. This is a Flapjack
infrastructure fact and does not assert correspondence with HOL. -/
namespace Flapjack.Compiler.Backend.WordBignum

theorem generateStubs_succeeds (width : Nat) [NeZero width] (location : Nat) :
    ∃ result, generateStubs width location = some result := by
  obtain ⟨⟨body, label, reg, next, installed⟩, h⟩ :=
    compileBounded_succeeds 0 location 2 1 (location + 1, []) (mcIopCode width)
  exact ⟨_, by simp [generateStubs, h]; rfl⟩

end Flapjack.Compiler.Backend.WordBignum
