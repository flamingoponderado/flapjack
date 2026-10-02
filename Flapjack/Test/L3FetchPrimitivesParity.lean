import Flapjack.RiscV.L3.Defs.ReadInst
namespace Flapjack.Test
open Flapjack.RiscV.L3
-- Original pc_generic_equation, for every complete native state.
example (s : riscv_state) : PC s = s.c_PC s.procID := rfl
-- Original skip_generic_equation, for every word and complete native state.
example (v : BitVec 64) (s : riscv_state) :
    «write'Skip» v s = { s with c_Skip := holUpdate s.procID v s.c_Skip } := rfl
end Flapjack.Test
