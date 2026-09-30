import Flapjack.Compiler.Backend.RiscVConfig.RegisterNames
namespace Flapjack.Test.RiscVNamesExactParity
open Flapjack.Compiler.Backend.RiscVConfig
example : [riscvNameLookup 0, riscvNameLookup 1, riscvNameLookup 2, riscvNameLookup 3, riscvNameLookup 4, riscvNameLookup 10, riscvNameLookup 11, riscvNameLookup 12, riscvNameLookup 13, riscvNameLookup 27, riscvNameLookup 28, riscvNameLookup 29, riscvNameLookup 30, riscvNameLookup 5, riscvNameLookup 31, riscvNameLookup 32, riscvNameLookup 1000] = [1, 10, 11, 12, 13, 27, 28, 29, 30, 0, 2, 3, 4, 5, 31, 32, 1000] := by
  simp [riscvNameLookup_eq, Flapjack.RiscV.riscvRegisterName]
end Flapjack.Test.RiscVNamesExactParity
