import Flapjack.Misc.Sptree
import Flapjack.HolRef

namespace Flapjack.Compiler.Backend.RiscVConfig

@[hol "cakeml/compiler/backend/riscv/riscv_configScript.sml" "riscv_names_def" 10]
def riscvNames : Flapjack.Spt Nat :=
  (Flapjack.sptInsert 0 1 (Flapjack.sptInsert 1 10 (Flapjack.sptInsert 2 11 (Flapjack.sptInsert 3 12 (Flapjack.sptInsert 4 13 (Flapjack.sptInsert 10 27 (Flapjack.sptInsert 11 28 (Flapjack.sptInsert 12 29 (Flapjack.sptInsert 13 30 (Flapjack.sptInsert 27 0 (Flapjack.sptInsert 28 2 (Flapjack.sptInsert 29 3 (Flapjack.sptInsert 30 4 .ln)))))))))))))

/-- Exact-tree identity-default projection used at the production naming boundary.
This is local infrastructure combining riscv_names with misc tlookup. -/
def riscvNameLookup (register : Nat) : Nat :=
  (Flapjack.sptLookup register riscvNames).getD register

end Flapjack.Compiler.Backend.RiscVConfig
