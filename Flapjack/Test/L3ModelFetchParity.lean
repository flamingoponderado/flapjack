import Flapjack.RiscV.L3.Defs.Fetch
namespace Flapjack.Test.L3ModelFetchParity
open Flapjack.RiscV.L3

example (s : riscv_state) (h : (PC s).getLsbD 0 = true) :
    Fetch () s = (.F_Error (.Internal (.FETCH_MISALIGNED (PC s))), s) := by
  simp [Fetch, h]

-- Successful physical fetch cannot mutate any memory byte, independent of VM
-- compatibility configuration or the fetched instruction's opcode.
example (s : riscv_state) :
    (Fetch () s).2.MEM8 = s.MEM8 := by
  simp [Fetch, translateAddr, rawReadInst, «write'Delta», «write'Skip»] <;>
    split <;> (try split) <;> simp_all

end Flapjack.Test.L3ModelFetchParity
