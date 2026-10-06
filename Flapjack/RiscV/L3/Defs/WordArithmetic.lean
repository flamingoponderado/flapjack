import Flapjack.RiscV.L3.Defs.IntegerLoadMode
import Flapjack.RiscV.L3.Defs.SystemSignals

/-! Complete ADDIW equation. RV32 signals Illegal_Instr. ADDIW sums at width64
before low32 extraction and sign-extends to width64; the mode-returned state is
used. ADDW/SUBW are absent on riscv-mi. -/
namespace Flapjack.RiscV.L3

noncomputable def «dfn'ADDIW» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, imm)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if v then (signalException ExceptionType.Illegal_Instr s) else ((«write'GPR» ((((BitVec.signExtend 64 ((holWordExtract 32 31 0 (((GPR rs1 s) + (BitVec.signExtend 64 imm))))))), rd)) s)))))

end Flapjack.RiscV.L3
