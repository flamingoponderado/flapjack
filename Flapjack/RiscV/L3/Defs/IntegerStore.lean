import Flapjack.RiscV.L3.Defs.IntegerLoadMode
import Flapjack.RiscV.L3.Defs.AddressException
import Flapjack.RiscV.L3.Defs.MMU.Translate
namespace Flapjack.RiscV.L3

/-- Literal source7325-7354: complete SW, fixed word5 rs1/rs2 and word12
offset, arbitrary native state. Signed offset is added to GPR rs1 with word64
wrap. Data/Write translation forwards its returned state to both Store_AMO_Fault
with the original virtual address and rs2 read/four-byte rawWriteData. No mode
or alignment guard is added, and no success/core-bound premise is assumed. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'SW_def"]
noncomputable def «dfn'SW» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rs1, (rs2, offs)) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := ((GPR rs1 state) + (BitVec.signExtend 64 offs)); (match (translateAddr ((v, (fetchType.Data, accessType.Write))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v) s) | some pAddr => (rawWriteData ((pAddr, (((GPR rs2 s), 4)))) s)))))

/-- Flapjack-only complete-state normal form, with no separately named HOL
original; every original branch remains and no premise is added. -/
theorem swWholeState (rs1 rs2 : BitVec 5) (offs : BitVec 12) (s : riscv_state) :
    «dfn'SW» (rs1,rs2,offs) s =
    let v := GPR rs1 s + BitVec.signExtend 64 offs
    let (addr,t) := translateAddr (v,fetchType.Data,accessType.Write) s
    match addr with
    | none => signalAddressException (.Store_AMO_Fault,v) t
    | some p => rawWriteData (p,GPR rs2 t,4) t := by
  rfl

/-- Literal source7355-7384: complete SH; full fixed word5 rs1/rs2,
signed word12 offset and arbitrary native state. Data/Write forwards its
returned state to rs2 read/2-byte rawWriteData or Store_AMO_Fault with
original virtual address. No mode or alignment guard is added. No alignment/success/core premise. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'SH_def"]
noncomputable def «dfn'SH» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rs1, (rs2, offs)) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := ((GPR rs1 state) + (BitVec.signExtend 64 offs)); (match (translateAddr ((v, (fetchType.Data, accessType.Write))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v) s) | some pAddr => (rawWriteData ((pAddr, (((GPR rs2 s), 2)))) s)))))

/-- Flapjack-only unconditional complete-state normal form; no standalone
HOL theorem is claimed and no original clause is removed. -/
theorem shWholeState (rs1 rs2 : BitVec 5) (offs : BitVec 12) (s : riscv_state) :
    «dfn'SH» (rs1,rs2,offs) s =
    let t := s
    let v := GPR rs1 t + BitVec.signExtend 64 offs
    let (addr,u) := translateAddr (v,fetchType.Data,accessType.Write) t
    match addr with
    | none => signalAddressException (.Store_AMO_Fault,v) u
    | some p => rawWriteData (p,GPR rs2 u,2) u := by
  rfl

/-- Literal source7385-7414: complete SB; full fixed word5 rs1/rs2,
signed word12 offset and arbitrary native state. Data/Write forwards its
returned state to rs2 read/1-byte rawWriteData or Store_AMO_Fault with
original virtual address. No mode or alignment guard is added. No alignment/success/core premise. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'SB_def"]
noncomputable def «dfn'SB» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rs1, (rs2, offs)) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := ((GPR rs1 state) + (BitVec.signExtend 64 offs)); (match (translateAddr ((v, (fetchType.Data, accessType.Write))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v) s) | some pAddr => (rawWriteData ((pAddr, (((GPR rs2 s), 1)))) s)))))

/-- Flapjack-only unconditional complete-state normal form; no standalone
HOL theorem is claimed and no original clause is removed. -/
theorem sbWholeState (rs1 rs2 : BitVec 5) (offs : BitVec 12) (s : riscv_state) :
    «dfn'SB» (rs1,rs2,offs) s =
    let t := s
    let v := GPR rs1 t + BitVec.signExtend 64 offs
    let (addr,u) := translateAddr (v,fetchType.Data,accessType.Write) t
    match addr with
    | none => signalAddressException (.Store_AMO_Fault,v) u
    | some p => rawWriteData (p,GPR rs2 u,1) u := by
  rfl

/-- Literal source7415-7455: complete SD; full fixed word5 rs1/rs2,
signed word12 offset and arbitrary native state. Data/Write forwards its
returned state to rs2 read/8-byte rawWriteData or Store_AMO_Fault with
original virtual address. The original mode guard runs first and all later routes use its returned state. No alignment/success/core premise. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'SD_def"]
noncomputable def «dfn'SD» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rs1, (rs2, offs)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if v then (signalException ExceptionType.Illegal_Instr s) else ((let v_1 : (BitVec 64) := ((GPR rs1 s) + (BitVec.signExtend 64 offs)); (match (translateAddr ((v_1, (fetchType.Data, accessType.Write))) s) with | (v0, s_1) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v_1) s_1) | some pAddr => (rawWriteData ((pAddr, (((GPR rs2 s_1), 8)))) s_1))))))))

/-- Flapjack-only unconditional complete-state normal form; no standalone
HOL theorem is claimed and no original clause is removed. -/
theorem sdWholeState (rs1 rs2 : BitVec 5) (offs : BitVec 12) (s : riscv_state) :
    «dfn'SD» (rs1,rs2,offs) s =
    let (is32,t) := in32BitMode () s
    if is32 then signalException .Illegal_Instr t else
    let v := GPR rs1 t + BitVec.signExtend 64 offs
    let (addr,u) := translateAddr (v,fetchType.Data,accessType.Write) t
    match addr with
    | none => signalAddressException (.Store_AMO_Fault,v) u
    | some p => rawWriteData (p,GPR rs2 u,8) u := by
  rfl

end Flapjack.RiscV.L3
