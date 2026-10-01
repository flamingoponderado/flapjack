import Flapjack.Compiler.Backend.Parmove
import Flapjack.Compiler.Backend.Parmove.StateToList

namespace Flapjack.Compiler.Backend.Parmove

/-- Injectivity is required only on endpoints in the three state lists.
The separate global equivalence preserves and reflects the temporary `NONE`.
Input and output payload carriers remain independent; this does not require
global injectivity, decidable equality, or any scheduler safety premise. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "inj_on_state_def"]
def injOnState {α β : Type} (f : Option α → Option β) (state : State α) : Prop :=
  let moves := stateToList state
  let endpoints := moves.map Prod.fst ++ moves.map Prod.snd
  (∀ x y, x ∈ endpoints ∧ y ∈ endpoints ∧ f x = f y → x = y) ∧
    (∀ x, f x = none ↔ x = none)

end Flapjack.Compiler.Backend.Parmove
