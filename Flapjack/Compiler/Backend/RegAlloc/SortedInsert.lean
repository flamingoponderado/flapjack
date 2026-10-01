import Flapjack.HolRef

namespace Flapjack.RegAlloc

/-- Literal adjacency-list insertion (`reg_allocScript.sml:184-189`) into a
`>`-descending list, skipping a duplicate. The accumulator holds the passed
(larger) prefix in reverse; HOL `REVERSE` is `List.reverse`. The definition is
total on arbitrary lists and assumes no ordering: on an unsorted list it
inserts before the first smaller element and may miss a later duplicate. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "sorted_insert_def"]
def sortedInsert (x : Nat) : List Nat → List Nat → List Nat
  | acc, [] => (x :: acc).reverse
  | acc, y :: ys =>
    if x = y then acc.reverse ++ y :: ys
    else if x > y then acc.reverse ++ x :: y :: ys
    else sortedInsert x (y :: acc) ys

end Flapjack.RegAlloc
