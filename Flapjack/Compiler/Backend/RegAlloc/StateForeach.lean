import Flapjack.Translator.Monadic.MonadBase

namespace Flapjack.RegAlloc
open Flapjack.Translator.Monadic.MonadBase

/-- Literal state-exception iteration. Each action runs from head to tail;
its successful result is discarded, while its returned state is threaded.
Failure retains its returned state and skips remaining actions. Element,
state, action-result and exception carriers remain independent. Production
allocator routing is separate work. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "st_ex_FOREACH_def"]
def stExForeach {state value result exception : Type} :
    List value → (value → M state result exception) → M state Unit exception
  | [], _ => ret ()
  | head :: tail, action => ignoreBind (action head) (stExForeach tail action)

end Flapjack.RegAlloc
