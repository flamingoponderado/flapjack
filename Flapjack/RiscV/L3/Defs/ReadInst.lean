import Flapjack.RiscV.L3.Defs.MMU.Primitives
namespace Flapjack.RiscV.L3

/-- Source review: riscvScript1260-1263 literal current-core c_PC read, fixed core word8/result word64 and entire native state. No procID/totalCore bound. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "PC_def"]
def PC (state : riscv_state) : (BitVec 64) :=
  (state.c_PC state.procID)

/-- Source review: riscvScript1281-1293 full c_Skip function update at procID with word64 value. All other state fields and all other core keys retained; no core bound or narrowed state. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "write'Skip_def"]
def «write'Skip» (value : (BitVec 64)) : (riscv_state → riscv_state) :=
  (fun (state : riscv_state) => (let r := state; { r with c_Skip := ((fun (_eta1 : ((BitVec 8) → (BitVec 64))) => (holUpdate state.procID value state.c_Skip))) r.c_Skip }))

end Flapjack.RiscV.L3
