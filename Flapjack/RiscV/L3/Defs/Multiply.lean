import Flapjack.RiscV.L3.Defs.IntegerLoadMode
import Flapjack.RiscV.L3.Defs.SystemSignals

/-! Full multiplication equations. High products preserve three mode queries,
128-bit intermediate widths and the literal per-operand signedness. MUL uses
full64 without a mode query; MULW retains the RV32 illegal route. -/
namespace Flapjack.RiscV.L3

noncomputable def «dfn'MULW» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if v then (signalException ExceptionType.Illegal_Instr s) else ((«write'GPR» ((((BitVec.signExtend 64 ((holWordExtract 32 31 0 ((BitVec.signExtend 64 ((((holWordExtract 32 31 0 (GPR rs1 s))) * ((holWordExtract 32 31 0 (GPR rs2 s))))))))))), rd)) s)))))

noncomputable def «dfn'MULHU» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (match (in32BitMode () s) with | (v0, s0) => (let prod : (BitVec 128) := (((if v then ((BitVec.setWidth 128 ((holWordExtract 32 31 0 (GPR rs1 s))))) else ((BitVec.setWidth 128 (GPR rs1 s))))) * ((if v0 then ((BitVec.setWidth 128 ((holWordExtract 32 31 0 (GPR rs2 s0))))) else ((BitVec.setWidth 128 (GPR rs2 s0)))))); (match (in32BitMode () s0) with | (v_1, s_1) => («write'GPR» ((((if v_1 then ((BitVec.setWidth 64 (holWordExtract 32 63 32 prod))) else (holWordExtract 64 127 64 prod))), rd)) s_1))))))

noncomputable def «dfn'MULHSU» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (match (in32BitMode () s) with | (v0, s0) => (let prod : (BitVec 128) := (((if v then ((BitVec.signExtend 128 ((holWordExtract 32 31 0 (GPR rs1 s))))) else ((BitVec.signExtend 128 (GPR rs1 s))))) * ((if v0 then ((BitVec.setWidth 128 ((holWordExtract 32 31 0 (GPR rs2 s0))))) else ((BitVec.setWidth 128 (GPR rs2 s0)))))); (match (in32BitMode () s0) with | (v_1, s_1) => («write'GPR» ((((if v_1 then ((BitVec.signExtend 64 (holWordExtract 32 63 32 prod))) else (holWordExtract 64 127 64 prod))), rd)) s_1))))))

noncomputable def «dfn'MULH» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (match (in32BitMode () s) with | (v0, s0) => (let prod : (BitVec 128) := (((BitVec.signExtend 128 ((if v then ((BitVec.signExtend 64 ((holWordExtract 32 31 0 (GPR rs1 s))))) else (GPR rs1 s))))) * ((BitVec.signExtend 128 ((if v0 then ((BitVec.signExtend 64 ((holWordExtract 32 31 0 (GPR rs2 s0))))) else (GPR rs2 s0)))))); (match (in32BitMode () s0) with | (v_1, s_1) => («write'GPR» ((((if v_1 then ((BitVec.signExtend 64 (holWordExtract 32 63 32 prod))) else ((BitVec.signExtend 64 (holWordExtract 64 127 64 prod))))), rd)) s_1))))))

def «dfn'MUL» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => («write'GPR» (((((GPR rs1 state) * (GPR rs2 state))), rd)) state))

end Flapjack.RiscV.L3
