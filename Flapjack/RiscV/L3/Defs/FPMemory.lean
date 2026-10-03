import Flapjack.RiscV.L3.Defs.MMU.Translate
import Flapjack.RiscV.L3.Defs.AddressException

/-! Full native FP loads and stores. Addresses signextend the word12 offset;
all success/failure paths retain the translation-returned state. Loads use direct
FPR writers without the arithmetic Dirty wrapper. Stores read the source FPR
after translation and write exactly four/eight bytes. No mode/alignment premise. -/
namespace Flapjack.RiscV.L3

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FSW_def"]
noncomputable def «dfn'FSW» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rs1, (rs2, offs)) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := ((GPR rs1 state) + (BitVec.signExtend 64 offs)); (match (translateAddr ((v, (fetchType.Data, accessType.Write))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v) s) | some pAddr => (rawWriteData ((pAddr, ((((BitVec.setWidth 64 (FPRS rs2 s))), 4)))) s)))))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FSD_def"]
noncomputable def «dfn'FSD» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rs1, (rs2, offs)) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := ((GPR rs1 state) + (BitVec.signExtend 64 offs)); (match (translateAddr ((v, (fetchType.Data, accessType.Write))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v) s) | some pAddr => (rawWriteData ((pAddr, (((FPRD rs2 s), 8)))) s)))))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FLW_def"]
noncomputable def «dfn'FLW» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, offs)) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := ((GPR rs1 state) + (BitVec.signExtend 64 offs)); (match (translateAddr ((v, (fetchType.Data, accessType.Read))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Load_Fault, v) s) | some pAddr => («write'FPRS» ((((holWordExtract 32 31 0 (rawReadData pAddr s))), rd)) s)))))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FLD_def"]
noncomputable def «dfn'FLD» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, offs)) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := ((GPR rs1 state) + (BitVec.signExtend 64 offs)); (match (translateAddr ((v, (fetchType.Data, accessType.Read))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Load_Fault, v) s) | some pAddr => («write'FPRD» (((rawReadData pAddr s), rd)) s)))))

end Flapjack.RiscV.L3
