import Flapjack.Compiler.Backend.BvlHandle.Helpers

/-! Source properties of handler-pass helper definitions. -/
namespace Flapjack.Compiler.Backend.BvlHandle.Proofs
open Bvl

/-- Every expression has strictly positive handler size. -/
@[hol "cakeml/compiler/backend/bvl_handleScript.sml" "handle_size_non_zero"]
theorem handleSize_nonzero (expression : Exp) : 0 < handleSize expression := by
  cases expression <;> simp [handleSize] <;> omega

end Flapjack.Compiler.Backend.BvlHandle.Proofs
