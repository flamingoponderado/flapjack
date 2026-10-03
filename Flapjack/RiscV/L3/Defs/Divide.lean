import Flapjack.RiscV.L3.Defs.IntegerLoadMode
import Flapjack.RiscV.L3.Defs.SystemSignals

/-! Complete native division/remainder equations, including explicit zero
divisors, signed truncation, DIVU two mode checks and W sign extension. -/
namespace Flapjack.RiscV.L3

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'REMW_def"]
noncomputable def «dfn'REMW» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if v then (signalException ExceptionType.Illegal_Instr s) else ((let v_1 : (BitVec 32) := (holWordExtract 32 31 0 (GPR rs1 s)); (let v0 : (BitVec 32) := (holWordExtract 32 31 0 (GPR rs2 s)); (if ((v0 == (BitVec.ofNat 32 0))) then ((«write'GPR» (((BitVec.signExtend 64 v_1), rd)) s)) else ((«write'GPR» ((((BitVec.signExtend 64 (BitVec.srem v_1 v0))), rd)) s)))))))))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'REMUW_def"]
noncomputable def «dfn'REMUW» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if v then (signalException ExceptionType.Illegal_Instr s) else ((let v_1 : (BitVec 32) := (holWordExtract 32 31 0 (GPR rs1 s)); (let v0 : (BitVec 32) := (holWordExtract 32 31 0 (GPR rs2 s)); (if ((v0 == (BitVec.ofNat 32 0))) then ((«write'GPR» (((BitVec.signExtend 64 v_1), rd)) s)) else ((«write'GPR» ((((BitVec.signExtend 64 (BitVec.umod v_1 v0))), rd)) s)))))))))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'REMU_def"]
def «dfn'REMU» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (if (((GPR rs2 state) == (BitVec.ofNat 64 0))) then ((«write'GPR» (((GPR rs1 state), rd)) state)) else ((«write'GPR» ((((BitVec.umod (GPR rs1 state) (GPR rs2 state))), rd)) state))))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'REM_def"]
def «dfn'REM» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (if (((GPR rs2 state) == (BitVec.ofNat 64 0))) then ((«write'GPR» (((GPR rs1 state), rd)) state)) else ((«write'GPR» ((((BitVec.srem (GPR rs1 state) (GPR rs2 state))), rd)) state))))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'DIVW_def"]
noncomputable def «dfn'DIVW» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if v then (signalException ExceptionType.Illegal_Instr s) else ((let v0 : (BitVec 32) := (holWordExtract 32 31 0 (GPR rs2 s)); (if ((v0 == (BitVec.ofNat 32 0))) then ((«write'GPR» ((((BitVec.signExtend 64 (BitVec.ofNat 1 1))), rd)) s)) else ((«write'GPR» ((((BitVec.signExtend 64 ((BitVec.sdiv ((holWordExtract 32 31 0 (GPR rs1 s))) v0)))), rd)) s))))))))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'DIVUW_def"]
noncomputable def «dfn'DIVUW» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if v then (signalException ExceptionType.Illegal_Instr s) else ((let v0 : (BitVec 32) := (holWordExtract 32 31 0 (GPR rs2 s)); (if ((v0 == (BitVec.ofNat 32 0))) then ((«write'GPR» ((((BitVec.signExtend 64 (BitVec.ofNat 1 1))), rd)) s)) else ((«write'GPR» ((((BitVec.signExtend 64 ((BitVec.udiv ((holWordExtract 32 31 0 (GPR rs1 s))) v0)))), rd)) s))))))))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'DIVU_def"]
noncomputable def «dfn'DIVU» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (match (in32BitMode () s) with | (v0, s0) => (let v0_1 : (BitVec 64) := (if v0 then ((BitVec.setWidth 64 ((holWordExtract 32 31 0 (GPR rs2 s0))))) else (GPR rs2 s0)); (if ((v0_1 == (BitVec.ofNat 64 0))) then ((«write'GPR» ((((BitVec.signExtend 64 (BitVec.ofNat 1 1))), rd)) s0)) else ((«write'GPR» ((((BitVec.udiv ((if v then ((BitVec.setWidth 64 ((holWordExtract 32 31 0 (GPR rs1 s))))) else (GPR rs1 s))) v0_1)), rd)) s0)))))))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'DIV_def"]
def «dfn'DIV» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (if (((GPR rs2 state) == (BitVec.ofNat 64 0))) then ((«write'GPR» ((((BitVec.signExtend 64 (BitVec.ofNat 1 1))), rd)) state)) else ((«write'GPR» ((((BitVec.sdiv (GPR rs1 state) (GPR rs2 state))), rd)) state))))

end Flapjack.RiscV.L3
