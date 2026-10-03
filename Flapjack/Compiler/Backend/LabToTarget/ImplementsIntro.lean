import Flapjack.SemanticsProps.Implements

namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.SemanticsPropsHOL

/-- Full original logical lift from a guarded non-Fail singleton equality.
The Boolean guard, both implications and precise true flag are retained. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "implements_intro_gen"]
theorem implementsIntroGen (b : Bool) (x : HolBehaviour) (y : BehaviourSetHOL) :
    (b = true ∧ x ≠ .fail → y = (fun behavior => behavior = x)) →
    b = true → implementsPrimeHOL true y (fun behavior => behavior = x) := by
  intro heq hb hfail result hresult
  have hx : x ≠ .fail := by
    intro hx
    exact hfail hx.symm
  have hy := heq ⟨hb,hx⟩
  change result = x
  rw [hy] at hresult
  exact hresult

end Flapjack.Compiler.Backend.LabToTarget
