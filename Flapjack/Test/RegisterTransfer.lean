module

public import Flapjack.RiscV.RegisterTransfer

-- Checks below run compiled code from these modules.
public meta import Flapjack.RiscV.RegisterNames
public meta import Flapjack.RiscV.RegisterTransfer
@[expose] public section

/-!
# RISC-V register-transfer bridge tests

These regressions exercise the concrete CakeML `riscv_names` transfer at the
boundary between internal stack-register state and hardware-register state.
They deliberately test the two exceptional cases: the internal link register
maps to hardware `x1`, while the internal zero register `27` maps to hardware
`x0`.
-/

namespace Flapjack.Test.RegisterTransfer

open Flapjack Flapjack.RiscV

#guard (riscvForward (0 : Fin 32)).val == 1
#guard (riscvForward (1 : Fin 32)).val == 10
#guard (riscvForward (27 : Fin 32)).val == 0
#guard (riscvInverse (0 : Fin 32)).val == 27
#guard (riscvInverse (10 : Fin 32)).val == 1

end Flapjack.Test.RegisterTransfer
