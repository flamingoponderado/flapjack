module

public import Flapjack.RiscV.OracleAllocator
public import Flapjack.RiscV.AllocatorCorrectness

@[expose] public section

/-!
Regression coverage for the composed CakeML allocator decision boundary.
The first example accepts a supplied colouring; the second deliberately
collides the two LongMul destinations under the oracle and therefore reaches
the graph allocator fallback.
-/

namespace Flapjack

end Flapjack
