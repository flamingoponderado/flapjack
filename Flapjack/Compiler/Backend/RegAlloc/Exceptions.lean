module

public import Flapjack.Basis.Pure.MlString
public import Flapjack.Compiler.Backend.RegAlloc.Carriers
public import Flapjack.Translator.Monadic.MonadBase

@[expose] public section

namespace Flapjack.RegAlloc

/-- HOL `string` is a list of the reviewed 256-element character carrier,
not a UTF-8 Lean String or an mlstring wrapper. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "state_exn"]
inductive StateException where
  | Fail (message : List Basis.Pure.MlString.HolChar)
  | Subscript
  deriving Repr, DecidableEq

end Flapjack.RegAlloc
