import Flapjack.Misc.Sptree

namespace Flapjack.WordAlloc

/-- Literal endpoint-presence cost. The map payload is never inspected: each
present endpoint contributes one, independently of its stored spill cost.
The executed allocator migration remains a separate dependency. -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "get_coalescecost_def"]
def getCoalesceCost {α : Type} (spillcost : Spt α)
    (move : Nat × Nat × (Nat × Nat)) : Nat × (Nat × Nat) :=
  let (n, p, (x, y)) := move
  let xcost := if (sptLookup x spillcost).isNone then 0 else 1
  let ycost := if (sptLookup y spillcost).isNone then 0 else 1
  (n * (10 * (p + 1) + xcost + ycost), (x, y))

end Flapjack.WordAlloc
