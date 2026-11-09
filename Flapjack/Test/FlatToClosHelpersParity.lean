import Flapjack.Compiler.Backend.FlatToClos.Helpers

/-! Kernel replays of `flat_to_clos_helpers_probe.out`. -/
namespace Flapjack.Test.FlatToClosHelpersParity
open Flapjack.Compiler.Backend Flapjack.Basis.Pure.MlString

-- The source helper accepts an arbitrary payload, not just a flat expression.
#guard FlatToClos.destPat [(.pvar (ofString "x"), (42 : Nat))] == some (ofString "x", 42)

-- Original constant folding reverses the extracted arguments.
#guard FlatToClos.smartCons .none 5
    [.op .none (.intOp (.const 7)) [], .op .none (.intOp (.const 9)) []] ==
  .op .none (.blockOp (.constant (.constCons 5 [.constInt 9, .constInt 7]))) []

end Flapjack.Test.FlatToClosHelpersParity
