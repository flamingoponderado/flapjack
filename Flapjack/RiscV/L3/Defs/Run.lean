import Flapjack.RiscV.L3.Defs
import Flapjack.RiscV.L3.Defs.ConditionalBranch
import Flapjack.RiscV.L3.Defs.ControlFetch
import Flapjack.RiscV.L3.Defs.Divide
import Flapjack.RiscV.L3.Defs.ImmediateALU
import Flapjack.RiscV.L3.Defs.ImmediateShift
import Flapjack.RiscV.L3.Defs.IntegerLoad
import Flapjack.RiscV.L3.Defs.IntegerStore
import Flapjack.RiscV.L3.Defs.Multiply
import Flapjack.RiscV.L3.Defs.RegisterALU
import Flapjack.RiscV.L3.Defs.RegisterShift
import Flapjack.RiscV.L3.Defs.SetLess
import Flapjack.RiscV.L3.Defs.SystemSignals
import Flapjack.RiscV.L3.Defs.UpperJump
import Flapjack.RiscV.L3.Defs.WordArithmetic

/-! RV64IM interpreter dispatch for the riscv-mi branch. -/
namespace Flapjack.RiscV.L3

noncomputable def Run (v0 : instruction) : (riscv_state → riscv_state) :=
  (fun (state : riscv_state) => (match v0 with
    | .ArithI v172 => (match v172 with
    | .ADDI v25 => («dfn'ADDI» v25 state)
    | .ADDIW v26 => («dfn'ADDIW» v26 state)
    | .ANDI v27 => («dfn'ANDI» v27 state)
    | .AUIPC v28 => («dfn'AUIPC» v28 state)
    | .LUI v29 => («dfn'LUI» v29 state)
    | .ORI v30 => («dfn'ORI» v30 state)
    | .SLTI v31 => («dfn'SLTI» v31 state)
    | .SLTIU v32 => («dfn'SLTIU» v32 state)
    | .XORI v33 => («dfn'XORI» v33 state))
    | .ArithR v173 => (match v173 with
    | .ADD v35 => («dfn'ADD» v35 state)
    | .ADDW v36 => («dfn'ADDW» v36 state)
    | .AND v37 => («dfn'AND» v37 state)
    | .OR v38 => («dfn'OR» v38 state)
    | .SLT v39 => («dfn'SLT» v39 state)
    | .SLTU v40 => («dfn'SLTU» v40 state)
    | .SUB v41 => («dfn'SUB» v41 state)
    | .SUBW v42 => («dfn'SUBW» v42 state)
    | .XOR v43 => («dfn'XOR» v43 state))
    | .Branch v174 => (match v174 with
    | .BEQ v45 => («dfn'BEQ» v45 state)
    | .BGE v46 => («dfn'BGE» v46 state)
    | .BGEU v47 => («dfn'BGEU» v47 state)
    | .BLT v48 => («dfn'BLT» v48 state)
    | .BLTU v49 => («dfn'BLTU» v49 state)
    | .BNE v50 => («dfn'BNE» v50 state)
    | .JAL v51 => («dfn'JAL» v51 state)
    | .JALR v52 => («dfn'JALR» v52 state))
    | .FENCE _v170 => state
    | .Internal v181 => (match v181 with
    | .FETCH_FAULT v120 => («dfn'FETCH_FAULT» v120 state)
    | .FETCH_MISALIGNED v121 => («dfn'FETCH_MISALIGNED» v121 state))
    | .Load v182 => (match v182 with
    | .LB v123 => («dfn'LB» v123 state)
    | .LBU v124 => («dfn'LBU» v124 state)
    | .LD v125 => («dfn'LD» v125 state)
    | .LH v126 => («dfn'LH» v126 state)
    | .LHU v127 => («dfn'LHU» v127 state)
    | .LW v128 => («dfn'LW» v128 state)
    | .LWU v129 => («dfn'LWU» v129 state))
    | .MulDiv v183 => (match v183 with
    | .DIV v131 => («dfn'DIV» v131 state)
    | .DIVU v132 => («dfn'DIVU» v132 state)
    | .DIVUW v133 => («dfn'DIVUW» v133 state)
    | .DIVW v134 => («dfn'DIVW» v134 state)
    | .MUL v135 => («dfn'MUL» v135 state)
    | .MULH v136 => («dfn'MULH» v136 state)
    | .MULHSU v137 => («dfn'MULHSU» v137 state)
    | .MULHU v138 => («dfn'MULHU» v138 state)
    | .MULW v139 => («dfn'MULW» v139 state)
    | .REM v140 => («dfn'REM» v140 state)
    | .REMU v141 => («dfn'REMU» v141 state)
    | .REMUW v142 => («dfn'REMUW» v142 state)
    | .REMW v143 => («dfn'REMW» v143 state))
    | .Shift v184 => (match v184 with
    | .SLL v145 => («dfn'SLL» v145 state)
    | .SLLI v146 => («dfn'SLLI» v146 state)
    | .SLLIW v147 => («dfn'SLLIW» v147 state)
    | .SLLW v148 => («dfn'SLLW» v148 state)
    | .SRA v149 => («dfn'SRA» v149 state)
    | .SRAI v150 => («dfn'SRAI» v150 state)
    | .SRAIW v151 => («dfn'SRAIW» v151 state)
    | .SRAW v152 => («dfn'SRAW» v152 state)
    | .SRL v153 => («dfn'SRL» v153 state)
    | .SRLI v154 => («dfn'SRLI» v154 state)
    | .SRLIW v155 => («dfn'SRLIW» v155 state)
    | .SRLW v156 => («dfn'SRLW» v156 state))
    | .Store v185 => (match v185 with
    | .SB v158 => («dfn'SB» v158 state)
    | .SD v159 => («dfn'SD» v159 state)
    | .SH v160 => («dfn'SH» v160 state)
    | .SW v161 => («dfn'SW» v161 state))
    | .System v186 => (match v186 with
    | .EBREAK => («dfn'EBREAK» state)
    | .ECALL => («dfn'ECALL» state)
    )
    | .UnknownInstruction => («dfn'UnknownInstruction» state)))

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_ADDI_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) (s : riscv_state) :
    Run (instruction.ArithI (ArithI.ADDI x)) s = «dfn'ADDI» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_ADDIW_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) (s : riscv_state) :
    Run (instruction.ArithI (ArithI.ADDIW x)) s = «dfn'ADDIW» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_ANDI_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) (s : riscv_state) :
    Run (instruction.ArithI (ArithI.ANDI x)) s = «dfn'ANDI» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_AUIPC_equation (x : ((BitVec 5) × (BitVec 20))) (s : riscv_state) :
    Run (instruction.ArithI (ArithI.AUIPC x)) s = «dfn'AUIPC» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_LUI_equation (x : ((BitVec 5) × (BitVec 20))) (s : riscv_state) :
    Run (instruction.ArithI (ArithI.LUI x)) s = «dfn'LUI» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_ORI_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) (s : riscv_state) :
    Run (instruction.ArithI (ArithI.ORI x)) s = «dfn'ORI» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_SLTI_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) (s : riscv_state) :
    Run (instruction.ArithI (ArithI.SLTI x)) s = «dfn'SLTI» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_SLTIU_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) (s : riscv_state) :
    Run (instruction.ArithI (ArithI.SLTIU x)) s = «dfn'SLTIU» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_XORI_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) (s : riscv_state) :
    Run (instruction.ArithI (ArithI.XORI x)) s = «dfn'XORI» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_ADD_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) (s : riscv_state) :
    Run (instruction.ArithR (ArithR.ADD x)) s = «dfn'ADD» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_ADDW_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) (s : riscv_state) :
    Run (instruction.ArithR (ArithR.ADDW x)) s = «dfn'ADDW» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_AND_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) (s : riscv_state) :
    Run (instruction.ArithR (ArithR.AND x)) s = «dfn'AND» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_OR_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) (s : riscv_state) :
    Run (instruction.ArithR (ArithR.OR x)) s = «dfn'OR» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_SLT_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) (s : riscv_state) :
    Run (instruction.ArithR (ArithR.SLT x)) s = «dfn'SLT» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_SLTU_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) (s : riscv_state) :
    Run (instruction.ArithR (ArithR.SLTU x)) s = «dfn'SLTU» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_SUB_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) (s : riscv_state) :
    Run (instruction.ArithR (ArithR.SUB x)) s = «dfn'SUB» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_SUBW_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) (s : riscv_state) :
    Run (instruction.ArithR (ArithR.SUBW x)) s = «dfn'SUBW» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_XOR_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) (s : riscv_state) :
    Run (instruction.ArithR (ArithR.XOR x)) s = «dfn'XOR» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_BEQ_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) (s : riscv_state) :
    Run (instruction.Branch (Branch.BEQ x)) s = «dfn'BEQ» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_BGE_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) (s : riscv_state) :
    Run (instruction.Branch (Branch.BGE x)) s = «dfn'BGE» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_BGEU_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) (s : riscv_state) :
    Run (instruction.Branch (Branch.BGEU x)) s = «dfn'BGEU» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_BLT_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) (s : riscv_state) :
    Run (instruction.Branch (Branch.BLT x)) s = «dfn'BLT» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_BLTU_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) (s : riscv_state) :
    Run (instruction.Branch (Branch.BLTU x)) s = «dfn'BLTU» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_BNE_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) (s : riscv_state) :
    Run (instruction.Branch (Branch.BNE x)) s = «dfn'BNE» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_JAL_equation (x : ((BitVec 5) × (BitVec 20))) (s : riscv_state) :
    Run (instruction.Branch (Branch.JAL x)) s = «dfn'JAL» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_JALR_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) (s : riscv_state) :
    Run (instruction.Branch (Branch.JALR x)) s = «dfn'JALR» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FENCE_equation (x : ((BitVec 5) × ((BitVec 5) × ((BitVec 4) × (BitVec 4))))) (s : riscv_state) :
    Run (instruction.FENCE x) s = s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FETCH_FAULT_equation (x : (BitVec 64)) (s : riscv_state) :
    Run (instruction.Internal (Internal.FETCH_FAULT x)) s = «dfn'FETCH_FAULT» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FETCH_MISALIGNED_equation (x : (BitVec 64)) (s : riscv_state) :
    Run (instruction.Internal (Internal.FETCH_MISALIGNED x)) s = «dfn'FETCH_MISALIGNED» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_LB_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) (s : riscv_state) :
    Run (instruction.Load (Load.LB x)) s = «dfn'LB» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_LBU_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) (s : riscv_state) :
    Run (instruction.Load (Load.LBU x)) s = «dfn'LBU» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_LD_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) (s : riscv_state) :
    Run (instruction.Load (Load.LD x)) s = «dfn'LD» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_LH_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) (s : riscv_state) :
    Run (instruction.Load (Load.LH x)) s = «dfn'LH» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_LHU_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) (s : riscv_state) :
    Run (instruction.Load (Load.LHU x)) s = «dfn'LHU» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_LW_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) (s : riscv_state) :
    Run (instruction.Load (Load.LW x)) s = «dfn'LW» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_LWU_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) (s : riscv_state) :
    Run (instruction.Load (Load.LWU x)) s = «dfn'LWU» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_DIV_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) (s : riscv_state) :
    Run (instruction.MulDiv (MulDiv.DIV x)) s = «dfn'DIV» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_DIVU_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) (s : riscv_state) :
    Run (instruction.MulDiv (MulDiv.DIVU x)) s = «dfn'DIVU» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_DIVUW_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) (s : riscv_state) :
    Run (instruction.MulDiv (MulDiv.DIVUW x)) s = «dfn'DIVUW» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_DIVW_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) (s : riscv_state) :
    Run (instruction.MulDiv (MulDiv.DIVW x)) s = «dfn'DIVW» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_MUL_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) (s : riscv_state) :
    Run (instruction.MulDiv (MulDiv.MUL x)) s = «dfn'MUL» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_MULH_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) (s : riscv_state) :
    Run (instruction.MulDiv (MulDiv.MULH x)) s = «dfn'MULH» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_MULHSU_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) (s : riscv_state) :
    Run (instruction.MulDiv (MulDiv.MULHSU x)) s = «dfn'MULHSU» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_MULHU_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) (s : riscv_state) :
    Run (instruction.MulDiv (MulDiv.MULHU x)) s = «dfn'MULHU» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_MULW_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) (s : riscv_state) :
    Run (instruction.MulDiv (MulDiv.MULW x)) s = «dfn'MULW» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_REM_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) (s : riscv_state) :
    Run (instruction.MulDiv (MulDiv.REM x)) s = «dfn'REM» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_REMU_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) (s : riscv_state) :
    Run (instruction.MulDiv (MulDiv.REMU x)) s = «dfn'REMU» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_REMUW_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) (s : riscv_state) :
    Run (instruction.MulDiv (MulDiv.REMUW x)) s = «dfn'REMUW» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_REMW_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) (s : riscv_state) :
    Run (instruction.MulDiv (MulDiv.REMW x)) s = «dfn'REMW» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_SLL_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) (s : riscv_state) :
    Run (instruction.Shift (Shift.SLL x)) s = «dfn'SLL» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_SLLI_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 6)))) (s : riscv_state) :
    Run (instruction.Shift (Shift.SLLI x)) s = «dfn'SLLI» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_SLLIW_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) (s : riscv_state) :
    Run (instruction.Shift (Shift.SLLIW x)) s = «dfn'SLLIW» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_SLLW_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) (s : riscv_state) :
    Run (instruction.Shift (Shift.SLLW x)) s = «dfn'SLLW» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_SRA_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) (s : riscv_state) :
    Run (instruction.Shift (Shift.SRA x)) s = «dfn'SRA» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_SRAI_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 6)))) (s : riscv_state) :
    Run (instruction.Shift (Shift.SRAI x)) s = «dfn'SRAI» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_SRAIW_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) (s : riscv_state) :
    Run (instruction.Shift (Shift.SRAIW x)) s = «dfn'SRAIW» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_SRAW_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) (s : riscv_state) :
    Run (instruction.Shift (Shift.SRAW x)) s = «dfn'SRAW» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_SRL_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) (s : riscv_state) :
    Run (instruction.Shift (Shift.SRL x)) s = «dfn'SRL» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_SRLI_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 6)))) (s : riscv_state) :
    Run (instruction.Shift (Shift.SRLI x)) s = «dfn'SRLI» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_SRLIW_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) (s : riscv_state) :
    Run (instruction.Shift (Shift.SRLIW x)) s = «dfn'SRLIW» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_SRLW_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) (s : riscv_state) :
    Run (instruction.Shift (Shift.SRLW x)) s = «dfn'SRLW» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_SB_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) (s : riscv_state) :
    Run (instruction.Store (Store.SB x)) s = «dfn'SB» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_SD_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) (s : riscv_state) :
    Run (instruction.Store (Store.SD x)) s = «dfn'SD» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_SH_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) (s : riscv_state) :
    Run (instruction.Store (Store.SH x)) s = «dfn'SH» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_SW_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) (s : riscv_state) :
    Run (instruction.Store (Store.SW x)) s = «dfn'SW» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_EBREAK_equation (s : riscv_state) :
    Run (instruction.System (System.EBREAK)) s = «dfn'EBREAK» s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_ECALL_equation (s : riscv_state) :
    Run (instruction.System (System.ECALL)) s = «dfn'ECALL» s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_UnknownInstruction_equation (s : riscv_state) :
    Run (instruction.UnknownInstruction) s = «dfn'UnknownInstruction» s := rfl

end Flapjack.RiscV.L3
