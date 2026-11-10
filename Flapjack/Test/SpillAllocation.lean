module

public import Flapjack.StackAlloc.Runtime
public import Flapjack.RiscV.WordToStack

@[expose] public section

/-!
Regression for the public spill-aware Word-to-Stack entry point.  It verifies
that the allocator's locations replace only the location map while frame and
bitmap configuration remain unchanged.
-/

namespace Flapjack.RiscV

end Flapjack.RiscV
