import Flapjack.Compiler.Backend.WordAlloc.SSASetup
import Mathlib.Data.List.Nodup
import Lean.Elab.Tactic.Omega

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Flapjack proof infrastructure for the local ALL_DISTINCT args obligation
in word_allocProofScript.sml:10164-10168. HOL has no standalone declaration for
this obligation, so this theorem has no HOL tag. The count is arbitrary. -/
theorem evenListNodup (count : Nat) : (evenList count).Nodup := by
  apply List.Nodup.map _ List.nodup_range
  intro left right equal
  simp only at equal
  omega

end Flapjack.Compiler.Backend.WordAlloc
