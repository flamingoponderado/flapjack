import Flapjack.HolRef

namespace Flapjack.Compiler.Backend.Parmove

/-- Map both endpoints of every pair in all three lists. HOL's definition
has independent arbitrary input/output element carriers, not only registers. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "map_state_def"]
def mapState {α β : Type} (f : α → β) :
    List (α × α) × List (α × α) × List (α × α) →
      List (β × β) × List (β × β) × List (β × β) :=
  let m := List.map (Prod.map f f)
  Prod.map m (Prod.map m m)

end Flapjack.Compiler.Backend.Parmove
