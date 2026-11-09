import Flapjack.Compiler.Backend.WordBignum.Generate
import Flapjack.Compiler.Backend.WordBignum.Proofs.FuelMonotone

/-! Totality of the captured-mini-program generator. This is a Flapjack
infrastructure fact and does not assert correspondence with HOL. -/
namespace Flapjack.Compiler.Backend.WordBignum

theorem generateStubs_succeeds (width : Nat) [NeZero width] (location : Nat) :
    ∃ result, generateStubs width location = some result := by
  exact ⟨assembleStubs location (compile location 2 1 (location + 1, []) (mcIopCode width)), rfl⟩

/-- The total entry point preserves the earlier bounded generation result. -/
theorem generateStubs_eq_bounded (width : Nat) [NeZero width] (location : Nat) :
    generateStubs width location =
      (compileBounded 0 location 2 1 (location + 1, []) (mcIopCode width)).map
        (assembleStubs location) := by
  simp [generateStubs, compileBounded_eq_compile]

end Flapjack.Compiler.Backend.WordBignum
