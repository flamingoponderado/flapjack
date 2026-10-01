import Flapjack.Misc.Max3
import Lean.Elab.Tactic.Omega

namespace Flapjack.WordAlloc

/-- Full HOL local three-way maximum equation. All arguments are natural
numbers; the branch-based reviewed definition is used without bound premises. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "max3_eq"]
theorem max3Eq : ∀ (x y z : Nat), max3HOL x y z = max x (max y z) := by
  intro x y z
  unfold max3HOL
  split <;> split <;> omega

end Flapjack.WordAlloc
