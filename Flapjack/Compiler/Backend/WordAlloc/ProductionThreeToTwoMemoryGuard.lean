import Flapjack.RiscV.WordDeadCode

namespace Flapjack.WordAlloc
open RiscV

/-- The complete actual three-to-two transform retains the extra memory guard.
Selected assignments introduce only Move/Assign nodes; all four optional-call
forms are included. This unconditional implementation-domain equality has no
HOL original and is not equality to HOL three-to-two semantics or a narrowed
allocation theorem. No source support or target-run premise is assumed. -/
theorem threeToTwoMemoryGuard {α : Type} (program : WordProg α) :
    allocatorMemorySupported (wordThreeToTwoReg program) = allocatorMemorySupported program := by
  fun_induction wordThreeToTwoReg program <;> simp_all [allocatorMemorySupported]

end Flapjack.WordAlloc
