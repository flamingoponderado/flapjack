import Flapjack.RiscV.L3.Defs.DecodeBits
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

/-- Source review: riscvScript4530-4570 tests low-byte bits 1 and 0, writes Skip 4 for Word32 or 2 for Half16, then concatenates bytes in little-endian order from the updated full state. Address additions wrap at 64 bits; no alignment or core-bound premise. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "rawReadInst_def"]
def rawReadInst (pAddr : (BitVec 64)) : (riscv_state → (rawInstType × riscv_state)) :=
  (fun (state : riscv_state) => (match (boolify8 (state.MEM8 pAddr)) with | (_b_7, _b_6, _b_5, _b_4, _b_3, _b_2, b_1, b_0) => (if (b_1 && b_0) then ((let s : riscv_state := («write'Skip» (BitVec.ofNat 64 4) state); (((rawInstType.Word ((BitVec.setWidth 32 (((s.MEM8 ((pAddr + (BitVec.ofNat 64 3))))) ++ ((BitVec.setWidth 24 (((s.MEM8 ((pAddr + (BitVec.ofNat 64 2))))) ++ ((BitVec.setWidth 16 (((s.MEM8 ((pAddr + (BitVec.ofNat 64 1))))) ++ (s.MEM8 pAddr)))))))))))), s))) else ((let s : riscv_state := («write'Skip» (BitVec.ofNat 64 2) state); (((rawInstType.Half ((BitVec.setWidth 16 (((s.MEM8 ((pAddr + (BitVec.ofNat 64 1))))) ++ (s.MEM8 pAddr)))))), s))))))

end Flapjack.RiscV.L3
