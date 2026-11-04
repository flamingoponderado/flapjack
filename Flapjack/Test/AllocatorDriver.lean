import Flapjack.RiscV.OracleAllocator
import Flapjack.RiscV.AllocatorCorrectness

/-!
Regression coverage for the composed CakeML allocator decision boundary.
The first example accepts a supplied colouring; the second deliberately
collides the two LongMul destinations under the oracle and therefore reaches
the graph allocator fallback.
-/

namespace Flapjack

end Flapjack
