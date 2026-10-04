import Flapjack.RiscV.L3.Defs.IntegerLoadMode
import Flapjack.RiscV.L3.Defs.SystemSignals

/-! Full literal register-shift equations. RV32 SLL retains full64 source;
SRL/SRA use low32 with unsigned/signed extension. Counts use low5 in RV32
and low6 otherwise. W forms trap in RV32 and signextend low32 results. -/
namespace Flapjack.RiscV.L3

noncomputable def «dfn'SRLW» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if v then (signalException ExceptionType.Illegal_Instr s) else ((«write'GPR» ((((BitVec.signExtend 64 ((((holWordExtract 32 31 0 (GPR rs1 s))) >>> ((BitVec.setWidth 32 ((holWordExtract 5 4 0 (GPR rs2 s))))).toNat)))), rd)) s)))))

noncomputable def «dfn'SRL» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if v then ((«write'GPR» ((((BitVec.setWidth 64 ((((holWordExtract 32 31 0 (GPR rs1 s))) >>> ((BitVec.setWidth 32 ((holWordExtract 5 4 0 (GPR rs2 s))))).toNat)))), rd)) s)) else ((«write'GPR» (((((GPR rs1 s) >>> ((BitVec.setWidth 64 ((holWordExtract 6 5 0 (GPR rs2 s))))).toNat)), rd)) s)))))

noncomputable def «dfn'SRAW» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if v then (signalException ExceptionType.Illegal_Instr s) else ((«write'GPR» ((((BitVec.signExtend 64 ((BitVec.sshiftRight ((holWordExtract 32 31 0 (GPR rs1 s))) ((BitVec.setWidth 32 ((holWordExtract 5 4 0 (GPR rs2 s))))).toNat)))), rd)) s)))))

noncomputable def «dfn'SRA» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if v then ((«write'GPR» ((((BitVec.signExtend 64 ((BitVec.sshiftRight ((holWordExtract 32 31 0 (GPR rs1 s))) ((BitVec.setWidth 32 ((holWordExtract 5 4 0 (GPR rs2 s))))).toNat)))), rd)) s)) else ((«write'GPR» ((((BitVec.sshiftRight (GPR rs1 s) ((BitVec.setWidth 64 ((holWordExtract 6 5 0 (GPR rs2 s))))).toNat)), rd)) s)))))

noncomputable def «dfn'SLLW» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if v then (signalException ExceptionType.Illegal_Instr s) else ((«write'GPR» ((((BitVec.signExtend 64 ((((holWordExtract 32 31 0 (GPR rs1 s))) <<< ((BitVec.setWidth 32 ((holWordExtract 5 4 0 (GPR rs2 s))))).toNat)))), rd)) s)))))

noncomputable def «dfn'SLL» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if v then ((«write'GPR» (((((GPR rs1 s) <<< ((BitVec.setWidth 64 ((holWordExtract 5 4 0 (GPR rs2 s))))).toNat)), rd)) s)) else ((«write'GPR» (((((GPR rs1 s) <<< ((BitVec.setWidth 64 ((holWordExtract 6 5 0 (GPR rs2 s))))).toNat)), rd)) s)))))

end Flapjack.RiscV.L3
