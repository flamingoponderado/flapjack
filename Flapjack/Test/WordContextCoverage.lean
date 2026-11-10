module

public import Flapjack.Pancake.LoopToWord

@[expose] public section

namespace Flapjack

private def coverageProbe : LoopProg Nat :=
  .assign 5 (.var 9)

end Flapjack
