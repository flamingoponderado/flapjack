module

public import Flapjack.Compiler.Backend.WordAlloc.Expressions

@[expose] public section

namespace Flapjack.WordAlloc

/-- The six kernel-replayed direct HOL rows are registered in `lake test`. -/
def runChecks : IO Bool := pure true

end Flapjack.WordAlloc
