module

public import Flapjack.Compiler.Backend.Semantics.ClosSem.Int

import all Flapjack.Compiler.Backend.Semantics.ClosSem.Int

@[expose] public section

/-! Kernel replay of signed division and boundary observations captured in
`scripts/hol-probes/clos_sem_int_probe.out`. -/
namespace Flapjack.Test.ClosSemIntParity
open Flapjack.Compiler.Backend.ClosSem

example : doIntApp .div [.number (-7), .number 3] = some (.number (-3)) := rfl
example : doIntApp .div [.number 7, .number (-3)] = some (.number (-3)) := rfl
example : doIntApp .mod [.number (-7), .number 3] = some (.number 2) := rfl
example : doIntApp .mod [.number 7, .number (-3)] = some (.number (-2)) := rfl
example : doIntApp .div [.number (-7), .number (-3)] = some (.number 2) := rfl
example : doIntApp .mod [.number (-7), .number (-3)] = some (.number (-1)) := rfl
example : doIntApp .div [.number (-6), .number 3] = some (.number (-2)) := rfl
example : doIntApp .mod [.number (-6), .number 3] = some (.number 0) := rfl
example : doIntApp .div [.number 7, .number 0] = none := rfl
example : doIntApp .mod [.number 7, .number 0] = none := rfl
example : doIntApp (.lessConstSmall 999999) [.number 1000000] = some (.block 0 []) := rfl
example : doIntApp (.lessConstSmall 1000000) [.number 0] = none := rfl
example : doIntApp (.lessConstSmall 0) [.number (-1)] = none := rfl
example : doIntApp (.lessConstSmall 999999) [.number 1000001] = none := rfl

end Flapjack.Test.ClosSemIntParity
