import Flapjack.HolRef

namespace Flapjack

/-- Projection preservation for every environment index and state.
The state and projection carriers remain independently arbitrary. -/
@[hol "cakeml/compiler/encoders/asm/asmPropsScript.sml" "interference_ok_def"]
def interferenceOk {state projection : Type}
    (env : Nat → state → state) (proj : state → projection) : Prop :=
  ∀ (i : Nat) (ms : state), proj (env i ms) = proj ms

end Flapjack
