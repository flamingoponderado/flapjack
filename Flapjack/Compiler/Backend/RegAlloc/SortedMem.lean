import Flapjack.HolRef

namespace Flapjack.RegAlloc

/-- Literal early-stop membership. The definition is total on arbitrary lists:
it does not assume descending order, and may reject an element occurring later
in an unsorted list. Production `cakeSortedMem` correspondence remains separate. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "sorted_mem_def"]
def sortedMem (x : Nat) : List Nat → Bool
  | [] => false
  | y :: ys => if x = y then true else if x > y then false else sortedMem x ys

end Flapjack.RegAlloc
