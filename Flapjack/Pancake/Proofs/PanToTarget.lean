import Flapjack.HolRef

/-!
# CakeML Pancake `pan_to_targetProof`

Counterpart of `cakeml/pancake/proofs/pan_to_targetProofScript.sml`. This
module holds standalone definition ports from that proof script. The
`compile_prog_max` wrapper and other large proof content remain open
(follow-up beads under `flapjack-28je`).
-/

namespace Flapjack.Pancake.Proofs.PanToTarget

/-- Exact HOL `option_lt`
    (`cakeml/pancake/proofs/pan_to_targetProofScript.sml:1157-1159`):
    `option_lt n0 NONE ⇔ T`, `option_lt NONE (SOME n1) ⇔ F`, and
    `option_lt (SOME n1) (SOME n2) ⇔ n1 < n2`. HOL `bool` is rendered by Lean
    `Bool`; the carrier is otherwise identity. -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "option_lt_def"]
def optionLt : Option Nat → Option Nat → Bool
  | _, none => true
  | none, some _ => false
  | some m, some n => m < n

end Flapjack.Pancake.Proofs.PanToTarget
