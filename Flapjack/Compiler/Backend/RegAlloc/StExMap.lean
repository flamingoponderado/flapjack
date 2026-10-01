import Flapjack.HolRef
import Flapjack.Translator.Monadic.MonadBase

namespace Flapjack.RegAlloc

open Flapjack.Translator.Monadic.MonadBase

/-- HOL `reg_alloc$st_ex_MAP` (`reg_allocScript.sml:148-156`): map a monadic
function over a list left to right; the `do` block is `st_ex_bind` twice and
`st_ex_return`, so the first failure stops the traversal with its state. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "st_ex_MAP_def"]
def stExMap {state value result exception : Type} (f : value → M state result exception) :
    List value → M state (List result) exception
  | [] => ret []
  | x :: xs => bind (f x) (fun fx => bind (stExMap f xs) (fun fxs => ret (fx :: fxs)))

end Flapjack.RegAlloc
