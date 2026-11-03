import Flapjack.RiscV.CorrectnessBackend
import Flapjack.RiscV.Ffi
import Flapjack.RiscV.Backend

/-! Regression coverage for the exact RISC-V instruction-step contracts. -/

namespace Flapjack.RiscV

def stepCountProgram : WordProg (Word 8) :=
  .seq (.assign 2 (.var 1)) (.return 0 [2])

end Flapjack.RiscV
