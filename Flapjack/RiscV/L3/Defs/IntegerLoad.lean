import Flapjack.RiscV.L3.Defs.AddressException
import Flapjack.RiscV.L3.Defs.IntegerLoadMode
import Flapjack.RiscV.L3.Defs.MMU.Translate
namespace Flapjack.RiscV.L3

/-! Complete original integer load equations, riscvScript7084-7324. Fixed rd/rs1
word5, signed offset word12 and full native word64 state are preserved. Only
LWU/LD apply the original in32BitMode guard and forward its returned state;
all clauses use Data/Read translation and forward its returned state to both
raw memory read/register update and Load_Fault with the original virtual address.
No alignment/core-bound/success premise or modern-ISA reinterpretation is added.
This section is not full Run/Next or executable compiler/runtime assembly. -/

/-- Source7084-7115: complete LW; low 32 bits with sign extension. No architecture/alignment guard is introduced. -/
noncomputable def «dfn'LW» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, offs)) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := ((GPR rs1 state) + (BitVec.signExtend 64 offs)); (match (translateAddr ((v, (fetchType.Data, accessType.Read))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Load_Fault, v) s) | some pAddr => («write'GPR» ((((BitVec.signExtend 64 ((holWordExtract 32 31 0 (rawReadData pAddr s))))), rd)) s)))))

/-- Source7116-7157: complete LWU; low 32 bits with zero extension. Original mode guard precedes address computation; its returned state is retained, including unspecified-mode behavior. -/
noncomputable def «dfn'LWU» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, offs)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if v then (signalException ExceptionType.Illegal_Instr s) else ((let v_1 : (BitVec 64) := ((GPR rs1 s) + (BitVec.signExtend 64 offs)); (match (translateAddr ((v_1, (fetchType.Data, accessType.Read))) s) with | (v0, s_1) => (match v0 with | none => (signalAddressException (ExceptionType.Load_Fault, v_1) s_1) | some pAddr => («write'GPR» ((((BitVec.setWidth 64 ((holWordExtract 32 31 0 (rawReadData pAddr s_1))))), rd)) s_1))))))))

/-- Source7158-7189: complete LH; low 16 bits with sign extension. No architecture/alignment guard is introduced. -/
noncomputable def «dfn'LH» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, offs)) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := ((GPR rs1 state) + (BitVec.signExtend 64 offs)); (match (translateAddr ((v, (fetchType.Data, accessType.Read))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Load_Fault, v) s) | some pAddr => («write'GPR» ((((BitVec.signExtend 64 ((holWordExtract 16 15 0 (rawReadData pAddr s))))), rd)) s)))))

/-- Source7190-7221: complete LHU; low 16 bits with zero extension. No architecture/alignment guard is introduced. -/
noncomputable def «dfn'LHU» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, offs)) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := ((GPR rs1 state) + (BitVec.signExtend 64 offs)); (match (translateAddr ((v, (fetchType.Data, accessType.Read))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Load_Fault, v) s) | some pAddr => («write'GPR» ((((BitVec.setWidth 64 ((holWordExtract 16 15 0 (rawReadData pAddr s))))), rd)) s)))))

/-- Source7222-7253: complete LB; low 8 bits with sign extension. No architecture/alignment guard is introduced. -/
noncomputable def «dfn'LB» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, offs)) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := ((GPR rs1 state) + (BitVec.signExtend 64 offs)); (match (translateAddr ((v, (fetchType.Data, accessType.Read))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Load_Fault, v) s) | some pAddr => («write'GPR» ((((BitVec.signExtend 64 ((holWordExtract 8 7 0 (rawReadData pAddr s))))), rd)) s)))))

/-- Source7254-7285: complete LBU; low 8 bits with zero extension. No architecture/alignment guard is introduced. -/
noncomputable def «dfn'LBU» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, offs)) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := ((GPR rs1 state) + (BitVec.signExtend 64 offs)); (match (translateAddr ((v, (fetchType.Data, accessType.Read))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Load_Fault, v) s) | some pAddr => («write'GPR» ((((BitVec.setWidth 64 ((holWordExtract 8 7 0 (rawReadData pAddr s))))), rd)) s)))))

/-- Source7286-7324: complete LD; low 64 bits with raw word64. Original mode guard precedes address computation; its returned state is retained, including unspecified-mode behavior. -/
noncomputable def «dfn'LD» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, offs)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if v then (signalException ExceptionType.Illegal_Instr s) else ((let v_1 : (BitVec 64) := ((GPR rs1 s) + (BitVec.signExtend 64 offs)); (match (translateAddr ((v_1, (fetchType.Data, accessType.Read))) s) with | (v0, s_1) => (match v0 with | none => (signalAddressException (ExceptionType.Load_Fault, v_1) s_1) | some pAddr => («write'GPR» (((rawReadData pAddr s_1), rd)) s_1))))))))

end Flapjack.RiscV.L3
