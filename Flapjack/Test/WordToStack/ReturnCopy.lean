import Flapjack.Stack

namespace Flapjack.Test

open Flapjack

/- CakeML's `num_stack_ret 1 [..,..]` is two: both values are copied from the
   previous frame, then those two temporary slots are freed before continuing. -/
example : stackNumReturnSlots 1 [10, 12] = 2 := by
  rfl

end Flapjack.Test
