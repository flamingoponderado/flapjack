import Flapjack.Basis.Pure.MlString
import Flapjack.Compiler.Backend.RegAlloc.Carriers
import Flapjack.Translator.Monadic.MonadBase

namespace Flapjack.RegAlloc

/-- HOL `string` is a list of the reviewed 256-element character carrier,
not a UTF-8 Lean String or an mlstring wrapper. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "state_exn"]
inductive StateException where
  | Fail (message : List Basis.Pure.MlString.HolChar)
  | Subscript
  deriving Repr, DecidableEq

end Flapjack.RegAlloc
