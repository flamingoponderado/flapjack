module

public import Flapjack.Compiler.Backend.Semantics.WordSem.CallHelpers

@[expose] public section

/-! The word semantics' termination limit is nonzero. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- The termination limit remains positive for every HOL word dimension. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "MustTerminate_limit_NOT_0"
  (word_dimension_as_width := width), simp]
theorem mustTerminateLimit_ne_zero (width : Nat) [NeZero width] :
    wordSemMustTerminateLimit width ≠ 0 := by
  have h : 0 < (2 : Nat) ^ width := Nat.two_pow_pos width
  simp only [wordSemMustTerminateLimit]
  omega

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
