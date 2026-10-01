import Flapjack.Translator.Monadic.MonadBase

namespace Flapjack.RegAlloc

open Flapjack.Translator.Monadic.MonadBase

/-- Literal state-exception list partition. Predicates run from head to tail;
each successful Boolean selects the accumulator to prepend to. Existing
accumulators are retained at the end of the reversed selected input lists.
Accepted bind propagates a failure together with its returned state and skips
all later predicates. Value, state and exception carriers remain independent.
This definition is a prerequisite for the native allocator phase proofs;
production allocator routing remains separate work. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "st_ex_PARTITION_def"]
def stExPartition {state value exception : Type}
    (predicate : value → M state Bool exception) :
    List value → List value → List value → M state (List value × List value) exception
  | [], yes, no => ret (yes, no)
  | head :: tail, yes, no =>
    bind (predicate head) (fun selected =>
      if selected then stExPartition predicate tail (head :: yes) no
      else stExPartition predicate tail yes (head :: no))

end Flapjack.RegAlloc
