import Flapjack.RiscV.L3.Defs.IntegerLoadMode
import Flapjack.RiscV.L3.Defs.SystemSignals

/-! Full immediate-shift equations: regular word6 immediates reject bit5 in
RV32; W word5 immediates trap in RV32. SRLI/SRAI thread a second mode check
after legality. Source words and all extensions follow the literal model. -/
namespace Flapjack.RiscV.L3

noncomputable def «dfn'SRLIW» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, imm)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if v then (signalException ExceptionType.Illegal_Instr s) else ((«write'GPR» ((((BitVec.signExtend 64 ((((holWordExtract 32 31 0 (GPR rs1 s))) >>> imm.toNat)))), rd)) s)))))

noncomputable def «dfn'SRLI» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 6)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, imm)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if ((v && (imm.getLsbD 5))) then (signalException ExceptionType.Illegal_Instr s) else ((match (in32BitMode () s) with | (v_1, s_1) => («write'GPR» ((((((if v_1 then ((BitVec.setWidth 64 ((holWordExtract 32 31 0 (GPR rs1 s_1))))) else (GPR rs1 s_1))) >>> imm.toNat)), rd)) s_1))))))

noncomputable def «dfn'SRAIW» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, imm)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if v then (signalException ExceptionType.Illegal_Instr s) else ((«write'GPR» ((((BitVec.signExtend 64 ((BitVec.sshiftRight ((holWordExtract 32 31 0 (GPR rs1 s))) imm.toNat)))), rd)) s)))))

noncomputable def «dfn'SRAI» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 6)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, imm)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if ((v && (imm.getLsbD 5))) then (signalException ExceptionType.Illegal_Instr s) else ((match (in32BitMode () s) with | (v_1, s_1) => («write'GPR» ((((BitVec.sshiftRight ((if v_1 then ((BitVec.signExtend 64 ((holWordExtract 32 31 0 (GPR rs1 s_1))))) else (GPR rs1 s_1))) imm.toNat)), rd)) s_1))))))

noncomputable def «dfn'SLLIW» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, imm)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if v then (signalException ExceptionType.Illegal_Instr s) else ((«write'GPR» ((((BitVec.signExtend 64 ((((holWordExtract 32 31 0 (GPR rs1 s))) <<< imm.toNat)))), rd)) s)))))

noncomputable def «dfn'SLLI» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 6)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, imm)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if ((v && (imm.getLsbD 5))) then (signalException ExceptionType.Illegal_Instr s) else ((«write'GPR» (((((GPR rs1 s) <<< imm.toNat)), rd)) s)))))

end Flapjack.RiscV.L3
