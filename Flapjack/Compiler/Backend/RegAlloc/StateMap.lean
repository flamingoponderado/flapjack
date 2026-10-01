import Flapjack.Translator.Monadic.MonadBase

namespace Flapjack.RegAlloc

open Flapjack.Translator.Monadic.MonadBase

/-- Literal monadic list map. The head effect runs before the recursive tail;
the accepted bind retains the state returned by a failure and skips subsequent
effects. Source type independently quantifies input, result, state and exception
carriers, confirmed by the captured original type. Production allocator routing
and the rest of the generated state operations remain separate work. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "st_ex_MAP_def"]
def stExMap {state value result exception : Type}
    (f : value → M state result exception) : List value → M state (List result) exception
  | [] => ret []
  | head :: tail =>
    bind (f head) (fun value =>
      bind (stExMap f tail) (fun values => ret (value :: values)))

end Flapjack.RegAlloc
