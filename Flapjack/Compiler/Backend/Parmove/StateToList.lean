import Flapjack.HolRef

namespace Flapjack.Compiler.Backend.Parmove

/-- Flatten the three state lists in pending/active/emitted order. HOL's
carrier here is arbitrary element lists, broader than move states. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "state_to_list_def"]
def stateToList {α : Type} (state : List α × List α × List α) : List α :=
  (state.1 ++ state.2.1) ++ state.2.2

end Flapjack.Compiler.Backend.Parmove
