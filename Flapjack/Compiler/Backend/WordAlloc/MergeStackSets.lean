import Flapjack.Misc.Sptree

namespace Flapjack.WordAlloc

/-- Literal branch stack-set merge. The initial tree supplies only a domain;
its payload and the ignored initial fixed component remain unrestricted. -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "merge_stack_sets_def"]
def mergeStackSets {α β γ δ : Type} (initial : Spt γ × δ)
    (left right : Spt α × Spt β) : Spt α × Spt β :=
  let keep1 := sptInter right.1 (sptInter left.1 initial.1)
  let keep2 := sptUnion (sptDifference left.1 initial.1)
    (sptDifference right.1 initial.1)
  (sptUnion keep1 keep2, sptUnion left.2 right.2)

end Flapjack.WordAlloc
