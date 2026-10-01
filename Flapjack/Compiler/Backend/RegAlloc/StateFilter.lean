import Flapjack.Translator.Monadic.MonadBase

namespace Flapjack.RegAlloc

open Flapjack.Translator.Monadic.MonadBase

/-- Literal state-exception list filter (`reg_allocScript.sml:170-179`).
Predicates run from head to tail; each successful `true` prepends the element
to the accumulator, so selected elements end up reversed in front of the
initial accumulator, which is returned unchanged on the empty list. The
accepted bind propagates a failure together with its returned state and skips
all later predicates. Value, state and exception carriers are independent, as
in the original type. Production allocator routing remains separate work. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "st_ex_FILTER_def"]
def stExFilter {state value exception : Type}
    (predicate : value → M state Bool exception) :
    List value → List value → M state (List value) exception
  | [], acc => ret acc
  | head :: tail, acc =>
    bind (predicate head) (fun selected =>
      if selected then stExFilter predicate tail (head :: acc)
      else stExFilter predicate tail acc)

end Flapjack.RegAlloc
