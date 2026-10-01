import Flapjack.HolRef

namespace Flapjack.WordAlloc

/-- Original natural-number spill cost. The five counters retain their source
product order, and the tail multiplier applies to the entire weighted sum. -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "get_spillcost_def"]
def getSpillCost (counts : Nat × Nat × Nat × Nat × Nat) (isTail : Bool) : Nat :=
  let (calls, leftRegisters, leftMemory, rightRegisters, rightMemory) := counts
  (calls + 2 * leftRegisters + 4 * leftMemory +
    2 * rightRegisters + 4 * rightMemory) * (if isTail then 5 else 1)

end Flapjack.WordAlloc
