module

public import Flapjack.Compiler.Backend.DataToWord.Variables

@[expose] public section

/-! Bounds on variable numbering used by the garbage-collector proof. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

/-- Adjusted data-variable slots cannot be the reserved slot 15. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "adjust_var_not_15", simp]
theorem adjustVar_ne_fifteen (a2 : Nat) : adjustVar a2 ≠ 15 := by
  simp only [adjustVar]
  omega

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
