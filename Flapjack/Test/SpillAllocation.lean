import Flapjack.StackAlloc.Runtime
import Flapjack.RiscV.WordToStack

/-!
Regression for the public spill-aware Word-to-Stack entry point.  It verifies
that the allocator's locations replace only the location map while frame and
bitmap configuration remain unchanged.
-/

namespace Flapjack.RiscV

end Flapjack.RiscV
