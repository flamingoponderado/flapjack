import Flapjack.Compiler.Backend.Parmove.StateToList

namespace Flapjack.Compiler.Backend.Parmove

/-- HOL `inj_on_state_def` (parmoveScript.sml:1090-1096): a function is
injective on the flattened state (both endpoints of every move) and only maps
`NONE` to `NONE`. The carrier is the literal list of optional pairs, so the
function is compared on `Option α` values. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "inj_on_state_def"]
def injOnState {α β : Type} (f : Option α → Option β)
    (p : List (Option α × Option α) × List (Option α × Option α) ×
      List (Option α × Option α)) : Prop :=
  let ls0 := stateToList p
  let ls := ls0.map Prod.fst ++ ls0.map Prod.snd
  (∀ x y, x ∈ ls → y ∈ ls → f x = f y → x = y) ∧
    (∀ x, f x = none ↔ x = none)

end Flapjack.Compiler.Backend.Parmove
