import Flapjack.RiscV.L3.Defs.IntegerLoadMode
import Flapjack.RiscV.L3.Defs.SystemSignals

/-! Complete word arithmetic equations. RV32 signals Illegal_Instr. ADDIW
sums at width64 before low32 extraction; ADDW/SUBW compute at width32.
All successful results sign-extend to width64; the mode-returned state is used. -/
namespace Flapjack.RiscV.L3

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'SUBW_def"]
noncomputable def «dfn'SUBW» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if v then (signalException ExceptionType.Illegal_Instr s) else ((«write'GPR» ((((BitVec.signExtend 64 ((((holWordExtract 32 31 0 (GPR rs1 s))) - ((holWordExtract 32 31 0 (GPR rs2 s))))))), rd)) s)))))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'ADDW_def"]
noncomputable def «dfn'ADDW» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if v then (signalException ExceptionType.Illegal_Instr s) else ((«write'GPR» ((((BitVec.signExtend 64 ((((holWordExtract 32 31 0 (GPR rs1 s))) + ((holWordExtract 32 31 0 (GPR rs2 s))))))), rd)) s)))))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'ADDIW_def"]
noncomputable def «dfn'ADDIW» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, imm)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if v then (signalException ExceptionType.Illegal_Instr s) else ((«write'GPR» ((((BitVec.signExtend 64 ((holWordExtract 32 31 0 (((GPR rs1 s) + (BitVec.signExtend 64 imm))))))), rd)) s)))))

end Flapjack.RiscV.L3
