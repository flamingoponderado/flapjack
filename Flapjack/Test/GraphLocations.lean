module

public import Flapjack.RiscV.AllocatorCorrectness

@[expose] public section

/-! Regression coverage for graph-allocation source locations. -/

namespace Flapjack

def graphLocationTestAllocation : WordGraphAllocation :=
  { bijection :=
      { toNode := [(7, 0)], fromNode := [(0, 7)], next := 1 }
    initialTags := []
    graph := { adjacency := [], tags := [], dimension := 1 }
    colouring := []
    parents := [] }

end Flapjack
