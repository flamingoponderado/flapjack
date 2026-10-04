import Flapjack.RiscV.L3.Defs.IntegerLoadMode

/-! Full original set-less-than equations. RV32 SLTU zeroextends low32;
RV32 SLTIU signextends low32, preserving the literal source asymmetry.
Register forms thread two mode checks; immediate forms thread one. -/
namespace Flapjack.RiscV.L3

noncomputable def «dfn'SLTU» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (match (in32BitMode () s) with | (v0, s0) => («write'GPR» ((((holV2w 64 ((((BitVec.ult ((if v then ((BitVec.setWidth 64 ((holWordExtract 32 31 0 (GPR rs1 s))))) else (GPR rs1 s))) ((if v0 then ((BitVec.setWidth 64 ((holWordExtract 32 31 0 (GPR rs2 s0))))) else (GPR rs2 s0))))) :: (([] : (List Bool))))))), rd)) s0))))

noncomputable def «dfn'SLT» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (match (in32BitMode () s) with | (v0, s0) => («write'GPR» ((((holV2w 64 ((((BitVec.slt ((if v then ((BitVec.signExtend 64 ((holWordExtract 32 31 0 (GPR rs1 s))))) else (GPR rs1 s))) ((if v0 then ((BitVec.signExtend 64 ((holWordExtract 32 31 0 (GPR rs2 s0))))) else (GPR rs2 s0))))) :: (([] : (List Bool))))))), rd)) s0))))

noncomputable def «dfn'SLTIU» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, imm)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => («write'GPR» ((((holV2w 64 ((((BitVec.ult ((if v then ((BitVec.signExtend 64 ((holWordExtract 32 31 0 (GPR rs1 s))))) else (GPR rs1 s))) (BitVec.signExtend 64 imm))) :: (([] : (List Bool))))))), rd)) s)))

noncomputable def «dfn'SLTI» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, imm)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => («write'GPR» ((((holV2w 64 ((((BitVec.slt ((if v then ((BitVec.signExtend 64 ((holWordExtract 32 31 0 (GPR rs1 s))))) else (GPR rs1 s))) (BitVec.signExtend 64 imm))) :: (([] : (List Bool))))))), rd)) s)))

end Flapjack.RiscV.L3
