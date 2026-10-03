import Flapjack.RiscV.L3.Defs
import Flapjack.RiscV.L3.Defs.AMOArithmetic
import Flapjack.RiscV.L3.Defs.AMOMinMax
import Flapjack.RiscV.L3.Defs.AMOSwap
import Flapjack.RiscV.L3.Defs.CSRInstructions
import Flapjack.RiscV.L3.Defs.ConditionalBranch
import Flapjack.RiscV.L3.Defs.ControlFetch
import Flapjack.RiscV.L3.Defs.Divide
import Flapjack.RiscV.L3.Defs.FPBits
import Flapjack.RiscV.L3.Defs.FPMemory
import Flapjack.RiscV.L3.Defs.ImmediateALU
import Flapjack.RiscV.L3.Defs.ImmediateShift
import Flapjack.RiscV.L3.Defs.IntegerLoad
import Flapjack.RiscV.L3.Defs.IntegerStore
import Flapjack.RiscV.L3.Defs.LRSC
import Flapjack.RiscV.L3.Defs.MMU.Flush
import Flapjack.RiscV.L3.Defs.Multiply
import Flapjack.RiscV.L3.Defs.RegisterALU
import Flapjack.RiscV.L3.Defs.RegisterShift
import Flapjack.RiscV.L3.Defs.SetLess
import Flapjack.RiscV.L3.Defs.SystemSignals
import Flapjack.RiscV.L3.Defs.UpperJump
import Flapjack.RiscV.L3.Defs.WordArithmetic

/-! Complete native Run dispatcher from original riscvScript10755.
All original instruction constructors retain their exact handler and payload.
FENCE/FENCE_I/WFI return the unchanged state. Real-dependent FP handlers
inherit SOUNDNESS item 8, rather than imposing any premise on Run. -/
namespace Flapjack.RiscV.L3

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "Run_def"]
noncomputable def Run (v0 : instruction) : (riscv_state → riscv_state) :=
  (fun (state : riscv_state) => (match v0 with
    | .AMO v => (match v with
    | .AMOADD_D v2 => («dfn'AMOADD_D» v2 state)
    | .AMOADD_W v3 => («dfn'AMOADD_W» v3 state)
    | .AMOAND_D v4 => («dfn'AMOAND_D» v4 state)
    | .AMOAND_W v5 => («dfn'AMOAND_W» v5 state)
    | .AMOMAXU_D v6 => («dfn'AMOMAXU_D» v6 state)
    | .AMOMAXU_W v7 => («dfn'AMOMAXU_W» v7 state)
    | .AMOMAX_D v8 => («dfn'AMOMAX_D» v8 state)
    | .AMOMAX_W v9 => («dfn'AMOMAX_W» v9 state)
    | .AMOMINU_D v10 => («dfn'AMOMINU_D» v10 state)
    | .AMOMINU_W v11 => («dfn'AMOMINU_W» v11 state)
    | .AMOMIN_D v12 => («dfn'AMOMIN_D» v12 state)
    | .AMOMIN_W v13 => («dfn'AMOMIN_W» v13 state)
    | .AMOOR_D v14 => («dfn'AMOOR_D» v14 state)
    | .AMOOR_W v15 => («dfn'AMOOR_W» v15 state)
    | .AMOSWAP_D v16 => («dfn'AMOSWAP_D» v16 state)
    | .AMOSWAP_W v17 => («dfn'AMOSWAP_W» v17 state)
    | .AMOXOR_D v18 => («dfn'AMOXOR_D» v18 state)
    | .AMOXOR_W v19 => («dfn'AMOXOR_W» v19 state)
    | .LR_D v20 => («dfn'LR_D» v20 state)
    | .LR_W v21 => («dfn'LR_W» v21 state)
    | .SC_D v22 => («dfn'SC_D» v22 state)
    | .SC_W v23 => («dfn'SC_W» v23 state))
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
    | .FArith v175 => (match v175 with
    | .FADD_D v54 => («dfn'FADD_D» v54 state)
    | .FADD_S v55 => («dfn'FADD_S» v55 state)
    | .FDIV_D v56 => («dfn'FDIV_D» v56 state)
    | .FDIV_S v57 => («dfn'FDIV_S» v57 state)
    | .FEQ_D v58 => («dfn'FEQ_D» v58 state)
    | .FEQ_S v59 => («dfn'FEQ_S» v59 state)
    | .FLE_D v60 => («dfn'FLE_D» v60 state)
    | .FLE_S v61 => («dfn'FLE_S» v61 state)
    | .FLT_D v62 => («dfn'FLT_D» v62 state)
    | .FLT_S v63 => («dfn'FLT_S» v63 state)
    | .FMADD_D v64 => («dfn'FMADD_D» v64 state)
    | .FMADD_S v65 => («dfn'FMADD_S» v65 state)
    | .FMAX_D v66 => («dfn'FMAX_D» v66 state)
    | .FMAX_S v67 => («dfn'FMAX_S» v67 state)
    | .FMIN_D v68 => («dfn'FMIN_D» v68 state)
    | .FMIN_S v69 => («dfn'FMIN_S» v69 state)
    | .FMSUB_D v70 => («dfn'FMSUB_D» v70 state)
    | .FMSUB_S v71 => («dfn'FMSUB_S» v71 state)
    | .FMUL_D v72 => («dfn'FMUL_D» v72 state)
    | .FMUL_S v73 => («dfn'FMUL_S» v73 state)
    | .FNMADD_D v74 => («dfn'FNMADD_D» v74 state)
    | .FNMADD_S v75 => («dfn'FNMADD_S» v75 state)
    | .FNMSUB_D v76 => («dfn'FNMSUB_D» v76 state)
    | .FNMSUB_S v77 => («dfn'FNMSUB_S» v77 state)
    | .FSQRT_D v78 => («dfn'FSQRT_D» v78 state)
    | .FSQRT_S v79 => («dfn'FSQRT_S» v79 state)
    | .FSUB_D v80 => («dfn'FSUB_D» v80 state)
    | .FSUB_S v81 => («dfn'FSUB_S» v81 state))
    | .FConv v176 => (match v176 with
    | .FCLASS_D v83 => («dfn'FCLASS_D» v83 state)
    | .FCLASS_S v84 => («dfn'FCLASS_S» v84 state)
    | .FCVT_D_L v85 => («dfn'FCVT_D_L» v85 state)
    | .FCVT_D_LU v86 => («dfn'FCVT_D_LU» v86 state)
    | .FCVT_D_S v87 => («dfn'FCVT_D_S» v87 state)
    | .FCVT_D_W v88 => («dfn'FCVT_D_W» v88 state)
    | .FCVT_D_WU v89 => («dfn'FCVT_D_WU» v89 state)
    | .FCVT_LU_D v90 => («dfn'FCVT_LU_D» v90 state)
    | .FCVT_LU_S v91 => («dfn'FCVT_LU_S» v91 state)
    | .FCVT_L_D v92 => («dfn'FCVT_L_D» v92 state)
    | .FCVT_L_S v93 => («dfn'FCVT_L_S» v93 state)
    | .FCVT_S_D v94 => («dfn'FCVT_S_D» v94 state)
    | .FCVT_S_L v95 => («dfn'FCVT_S_L» v95 state)
    | .FCVT_S_LU v96 => («dfn'FCVT_S_LU» v96 state)
    | .FCVT_S_W v97 => («dfn'FCVT_S_W» v97 state)
    | .FCVT_S_WU v98 => («dfn'FCVT_S_WU» v98 state)
    | .FCVT_WU_D v99 => («dfn'FCVT_WU_D» v99 state)
    | .FCVT_WU_S v100 => («dfn'FCVT_WU_S» v100 state)
    | .FCVT_W_D v101 => («dfn'FCVT_W_D» v101 state)
    | .FCVT_W_S v102 => («dfn'FCVT_W_S» v102 state)
    | .FMV_D_X v103 => («dfn'FMV_D_X» v103 state)
    | .FMV_S_X v104 => («dfn'FMV_S_X» v104 state)
    | .FMV_X_D v105 => («dfn'FMV_X_D» v105 state)
    | .FMV_X_S v106 => («dfn'FMV_X_S» v106 state)
    | .FSGNJN_D v107 => («dfn'FSGNJN_D» v107 state)
    | .FSGNJN_S v108 => («dfn'FSGNJN_S» v108 state)
    | .FSGNJX_D v109 => («dfn'FSGNJX_D» v109 state)
    | .FSGNJX_S v110 => («dfn'FSGNJX_S» v110 state)
    | .FSGNJ_D v111 => («dfn'FSGNJ_D» v111 state)
    | .FSGNJ_S v112 => («dfn'FSGNJ_S» v112 state))
    | .FENCE _v170 => state
    | .FENCE_I _v171 => state
    | .FPLoad v179 => (match v179 with
    | .FLD v114 => («dfn'FLD» v114 state)
    | .FLW v115 => («dfn'FLW» v115 state))
    | .FPStore v180 => (match v180 with
    | .FSD v117 => («dfn'FSD» v117 state)
    | .FSW v118 => («dfn'FSW» v118 state))
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
    | .CSRRC v163 => («dfn'CSRRC» v163 state)
    | .CSRRCI v164 => («dfn'CSRRCI» v164 state)
    | .CSRRS v165 => («dfn'CSRRS» v165 state)
    | .CSRRSI v166 => («dfn'CSRRSI» v166 state)
    | .CSRRW v167 => («dfn'CSRRW» v167 state)
    | .CSRRWI v168 => («dfn'CSRRWI» v168 state)
    | .EBREAK => («dfn'EBREAK» state)
    | .ECALL => («dfn'ECALL» state)
    | .ERET => («dfn'ERET» state)
    | .MRTS => («dfn'MRTS» state)
    | .SFENCE_VM v169 => («dfn'SFENCE_VM» v169 state)
    | .WFI => state)
    | .UnknownInstruction => («dfn'UnknownInstruction» state)))

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_AMOADD_D_equation (x : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) (s : riscv_state) :
    Run (instruction.AMO (AMO.AMOADD_D x)) s = «dfn'AMOADD_D» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_AMOADD_W_equation (x : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) (s : riscv_state) :
    Run (instruction.AMO (AMO.AMOADD_W x)) s = «dfn'AMOADD_W» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_AMOAND_D_equation (x : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) (s : riscv_state) :
    Run (instruction.AMO (AMO.AMOAND_D x)) s = «dfn'AMOAND_D» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_AMOAND_W_equation (x : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) (s : riscv_state) :
    Run (instruction.AMO (AMO.AMOAND_W x)) s = «dfn'AMOAND_W» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_AMOMAXU_D_equation (x : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) (s : riscv_state) :
    Run (instruction.AMO (AMO.AMOMAXU_D x)) s = «dfn'AMOMAXU_D» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_AMOMAXU_W_equation (x : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) (s : riscv_state) :
    Run (instruction.AMO (AMO.AMOMAXU_W x)) s = «dfn'AMOMAXU_W» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_AMOMAX_D_equation (x : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) (s : riscv_state) :
    Run (instruction.AMO (AMO.AMOMAX_D x)) s = «dfn'AMOMAX_D» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_AMOMAX_W_equation (x : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) (s : riscv_state) :
    Run (instruction.AMO (AMO.AMOMAX_W x)) s = «dfn'AMOMAX_W» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_AMOMINU_D_equation (x : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) (s : riscv_state) :
    Run (instruction.AMO (AMO.AMOMINU_D x)) s = «dfn'AMOMINU_D» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_AMOMINU_W_equation (x : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) (s : riscv_state) :
    Run (instruction.AMO (AMO.AMOMINU_W x)) s = «dfn'AMOMINU_W» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_AMOMIN_D_equation (x : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) (s : riscv_state) :
    Run (instruction.AMO (AMO.AMOMIN_D x)) s = «dfn'AMOMIN_D» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_AMOMIN_W_equation (x : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) (s : riscv_state) :
    Run (instruction.AMO (AMO.AMOMIN_W x)) s = «dfn'AMOMIN_W» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_AMOOR_D_equation (x : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) (s : riscv_state) :
    Run (instruction.AMO (AMO.AMOOR_D x)) s = «dfn'AMOOR_D» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_AMOOR_W_equation (x : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) (s : riscv_state) :
    Run (instruction.AMO (AMO.AMOOR_W x)) s = «dfn'AMOOR_W» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_AMOSWAP_D_equation (x : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) (s : riscv_state) :
    Run (instruction.AMO (AMO.AMOSWAP_D x)) s = «dfn'AMOSWAP_D» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_AMOSWAP_W_equation (x : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) (s : riscv_state) :
    Run (instruction.AMO (AMO.AMOSWAP_W x)) s = «dfn'AMOSWAP_W» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_AMOXOR_D_equation (x : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) (s : riscv_state) :
    Run (instruction.AMO (AMO.AMOXOR_D x)) s = «dfn'AMOXOR_D» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_AMOXOR_W_equation (x : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) (s : riscv_state) :
    Run (instruction.AMO (AMO.AMOXOR_W x)) s = «dfn'AMOXOR_W» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_LR_D_equation (x : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × (BitVec 5))))) (s : riscv_state) :
    Run (instruction.AMO (AMO.LR_D x)) s = «dfn'LR_D» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_LR_W_equation (x : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × (BitVec 5))))) (s : riscv_state) :
    Run (instruction.AMO (AMO.LR_W x)) s = «dfn'LR_W» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_SC_D_equation (x : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) (s : riscv_state) :
    Run (instruction.AMO (AMO.SC_D x)) s = «dfn'SC_D» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_SC_W_equation (x : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) (s : riscv_state) :
    Run (instruction.AMO (AMO.SC_W x)) s = «dfn'SC_W» x s := rfl

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
theorem Run_FADD_D_equation (x : ((BitVec 5) × ((BitVec 5) × ((BitVec 5) × (BitVec 3))))) (s : riscv_state) :
    Run (instruction.FArith (FArith.FADD_D x)) s = «dfn'FADD_D» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FADD_S_equation (x : ((BitVec 5) × ((BitVec 5) × ((BitVec 5) × (BitVec 3))))) (s : riscv_state) :
    Run (instruction.FArith (FArith.FADD_S x)) s = «dfn'FADD_S» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FDIV_D_equation (x : ((BitVec 5) × ((BitVec 5) × ((BitVec 5) × (BitVec 3))))) (s : riscv_state) :
    Run (instruction.FArith (FArith.FDIV_D x)) s = «dfn'FDIV_D» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FDIV_S_equation (x : ((BitVec 5) × ((BitVec 5) × ((BitVec 5) × (BitVec 3))))) (s : riscv_state) :
    Run (instruction.FArith (FArith.FDIV_S x)) s = «dfn'FDIV_S» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FEQ_D_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) (s : riscv_state) :
    Run (instruction.FArith (FArith.FEQ_D x)) s = «dfn'FEQ_D» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FEQ_S_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) (s : riscv_state) :
    Run (instruction.FArith (FArith.FEQ_S x)) s = «dfn'FEQ_S» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FLE_D_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) (s : riscv_state) :
    Run (instruction.FArith (FArith.FLE_D x)) s = «dfn'FLE_D» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FLE_S_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) (s : riscv_state) :
    Run (instruction.FArith (FArith.FLE_S x)) s = «dfn'FLE_S» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FLT_D_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) (s : riscv_state) :
    Run (instruction.FArith (FArith.FLT_D x)) s = «dfn'FLT_D» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FLT_S_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) (s : riscv_state) :
    Run (instruction.FArith (FArith.FLT_S x)) s = «dfn'FLT_S» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FMADD_D_equation (x : ((BitVec 5) × ((BitVec 5) × ((BitVec 5) × ((BitVec 5) × (BitVec 3)))))) (s : riscv_state) :
    Run (instruction.FArith (FArith.FMADD_D x)) s = «dfn'FMADD_D» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FMADD_S_equation (x : ((BitVec 5) × ((BitVec 5) × ((BitVec 5) × ((BitVec 5) × (BitVec 3)))))) (s : riscv_state) :
    Run (instruction.FArith (FArith.FMADD_S x)) s = «dfn'FMADD_S» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FMAX_D_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) (s : riscv_state) :
    Run (instruction.FArith (FArith.FMAX_D x)) s = «dfn'FMAX_D» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FMAX_S_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) (s : riscv_state) :
    Run (instruction.FArith (FArith.FMAX_S x)) s = «dfn'FMAX_S» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FMIN_D_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) (s : riscv_state) :
    Run (instruction.FArith (FArith.FMIN_D x)) s = «dfn'FMIN_D» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FMIN_S_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) (s : riscv_state) :
    Run (instruction.FArith (FArith.FMIN_S x)) s = «dfn'FMIN_S» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FMSUB_D_equation (x : ((BitVec 5) × ((BitVec 5) × ((BitVec 5) × ((BitVec 5) × (BitVec 3)))))) (s : riscv_state) :
    Run (instruction.FArith (FArith.FMSUB_D x)) s = «dfn'FMSUB_D» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FMSUB_S_equation (x : ((BitVec 5) × ((BitVec 5) × ((BitVec 5) × ((BitVec 5) × (BitVec 3)))))) (s : riscv_state) :
    Run (instruction.FArith (FArith.FMSUB_S x)) s = «dfn'FMSUB_S» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FMUL_D_equation (x : ((BitVec 5) × ((BitVec 5) × ((BitVec 5) × (BitVec 3))))) (s : riscv_state) :
    Run (instruction.FArith (FArith.FMUL_D x)) s = «dfn'FMUL_D» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FMUL_S_equation (x : ((BitVec 5) × ((BitVec 5) × ((BitVec 5) × (BitVec 3))))) (s : riscv_state) :
    Run (instruction.FArith (FArith.FMUL_S x)) s = «dfn'FMUL_S» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FNMADD_D_equation (x : ((BitVec 5) × ((BitVec 5) × ((BitVec 5) × ((BitVec 5) × (BitVec 3)))))) (s : riscv_state) :
    Run (instruction.FArith (FArith.FNMADD_D x)) s = «dfn'FNMADD_D» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FNMADD_S_equation (x : ((BitVec 5) × ((BitVec 5) × ((BitVec 5) × ((BitVec 5) × (BitVec 3)))))) (s : riscv_state) :
    Run (instruction.FArith (FArith.FNMADD_S x)) s = «dfn'FNMADD_S» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FNMSUB_D_equation (x : ((BitVec 5) × ((BitVec 5) × ((BitVec 5) × ((BitVec 5) × (BitVec 3)))))) (s : riscv_state) :
    Run (instruction.FArith (FArith.FNMSUB_D x)) s = «dfn'FNMSUB_D» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FNMSUB_S_equation (x : ((BitVec 5) × ((BitVec 5) × ((BitVec 5) × ((BitVec 5) × (BitVec 3)))))) (s : riscv_state) :
    Run (instruction.FArith (FArith.FNMSUB_S x)) s = «dfn'FNMSUB_S» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FSQRT_D_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 3)))) (s : riscv_state) :
    Run (instruction.FArith (FArith.FSQRT_D x)) s = «dfn'FSQRT_D» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FSQRT_S_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 3)))) (s : riscv_state) :
    Run (instruction.FArith (FArith.FSQRT_S x)) s = «dfn'FSQRT_S» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FSUB_D_equation (x : ((BitVec 5) × ((BitVec 5) × ((BitVec 5) × (BitVec 3))))) (s : riscv_state) :
    Run (instruction.FArith (FArith.FSUB_D x)) s = «dfn'FSUB_D» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FSUB_S_equation (x : ((BitVec 5) × ((BitVec 5) × ((BitVec 5) × (BitVec 3))))) (s : riscv_state) :
    Run (instruction.FArith (FArith.FSUB_S x)) s = «dfn'FSUB_S» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FCLASS_D_equation (x : ((BitVec 5) × (BitVec 5))) (s : riscv_state) :
    Run (instruction.FConv (FConv.FCLASS_D x)) s = «dfn'FCLASS_D» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FCLASS_S_equation (x : ((BitVec 5) × (BitVec 5))) (s : riscv_state) :
    Run (instruction.FConv (FConv.FCLASS_S x)) s = «dfn'FCLASS_S» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FCVT_D_L_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 3)))) (s : riscv_state) :
    Run (instruction.FConv (FConv.FCVT_D_L x)) s = «dfn'FCVT_D_L» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FCVT_D_LU_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 3)))) (s : riscv_state) :
    Run (instruction.FConv (FConv.FCVT_D_LU x)) s = «dfn'FCVT_D_LU» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FCVT_D_S_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 3)))) (s : riscv_state) :
    Run (instruction.FConv (FConv.FCVT_D_S x)) s = «dfn'FCVT_D_S» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FCVT_D_W_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 3)))) (s : riscv_state) :
    Run (instruction.FConv (FConv.FCVT_D_W x)) s = «dfn'FCVT_D_W» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FCVT_D_WU_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 3)))) (s : riscv_state) :
    Run (instruction.FConv (FConv.FCVT_D_WU x)) s = «dfn'FCVT_D_WU» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FCVT_LU_D_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 3)))) (s : riscv_state) :
    Run (instruction.FConv (FConv.FCVT_LU_D x)) s = «dfn'FCVT_LU_D» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FCVT_LU_S_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 3)))) (s : riscv_state) :
    Run (instruction.FConv (FConv.FCVT_LU_S x)) s = «dfn'FCVT_LU_S» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FCVT_L_D_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 3)))) (s : riscv_state) :
    Run (instruction.FConv (FConv.FCVT_L_D x)) s = «dfn'FCVT_L_D» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FCVT_L_S_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 3)))) (s : riscv_state) :
    Run (instruction.FConv (FConv.FCVT_L_S x)) s = «dfn'FCVT_L_S» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FCVT_S_D_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 3)))) (s : riscv_state) :
    Run (instruction.FConv (FConv.FCVT_S_D x)) s = «dfn'FCVT_S_D» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FCVT_S_L_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 3)))) (s : riscv_state) :
    Run (instruction.FConv (FConv.FCVT_S_L x)) s = «dfn'FCVT_S_L» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FCVT_S_LU_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 3)))) (s : riscv_state) :
    Run (instruction.FConv (FConv.FCVT_S_LU x)) s = «dfn'FCVT_S_LU» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FCVT_S_W_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 3)))) (s : riscv_state) :
    Run (instruction.FConv (FConv.FCVT_S_W x)) s = «dfn'FCVT_S_W» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FCVT_S_WU_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 3)))) (s : riscv_state) :
    Run (instruction.FConv (FConv.FCVT_S_WU x)) s = «dfn'FCVT_S_WU» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FCVT_WU_D_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 3)))) (s : riscv_state) :
    Run (instruction.FConv (FConv.FCVT_WU_D x)) s = «dfn'FCVT_WU_D» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FCVT_WU_S_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 3)))) (s : riscv_state) :
    Run (instruction.FConv (FConv.FCVT_WU_S x)) s = «dfn'FCVT_WU_S» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FCVT_W_D_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 3)))) (s : riscv_state) :
    Run (instruction.FConv (FConv.FCVT_W_D x)) s = «dfn'FCVT_W_D» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FCVT_W_S_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 3)))) (s : riscv_state) :
    Run (instruction.FConv (FConv.FCVT_W_S x)) s = «dfn'FCVT_W_S» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FMV_D_X_equation (x : ((BitVec 5) × (BitVec 5))) (s : riscv_state) :
    Run (instruction.FConv (FConv.FMV_D_X x)) s = «dfn'FMV_D_X» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FMV_S_X_equation (x : ((BitVec 5) × (BitVec 5))) (s : riscv_state) :
    Run (instruction.FConv (FConv.FMV_S_X x)) s = «dfn'FMV_S_X» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FMV_X_D_equation (x : ((BitVec 5) × (BitVec 5))) (s : riscv_state) :
    Run (instruction.FConv (FConv.FMV_X_D x)) s = «dfn'FMV_X_D» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FMV_X_S_equation (x : ((BitVec 5) × (BitVec 5))) (s : riscv_state) :
    Run (instruction.FConv (FConv.FMV_X_S x)) s = «dfn'FMV_X_S» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FSGNJN_D_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) (s : riscv_state) :
    Run (instruction.FConv (FConv.FSGNJN_D x)) s = «dfn'FSGNJN_D» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FSGNJN_S_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) (s : riscv_state) :
    Run (instruction.FConv (FConv.FSGNJN_S x)) s = «dfn'FSGNJN_S» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FSGNJX_D_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) (s : riscv_state) :
    Run (instruction.FConv (FConv.FSGNJX_D x)) s = «dfn'FSGNJX_D» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FSGNJX_S_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) (s : riscv_state) :
    Run (instruction.FConv (FConv.FSGNJX_S x)) s = «dfn'FSGNJX_S» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FSGNJ_D_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) (s : riscv_state) :
    Run (instruction.FConv (FConv.FSGNJ_D x)) s = «dfn'FSGNJ_D» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FSGNJ_S_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) (s : riscv_state) :
    Run (instruction.FConv (FConv.FSGNJ_S x)) s = «dfn'FSGNJ_S» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FENCE_equation (x : ((BitVec 5) × ((BitVec 5) × ((BitVec 4) × (BitVec 4))))) (s : riscv_state) :
    Run (instruction.FENCE x) s = s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FENCE_I_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) (s : riscv_state) :
    Run (instruction.FENCE_I x) s = s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FLD_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) (s : riscv_state) :
    Run (instruction.FPLoad (FPLoad.FLD x)) s = «dfn'FLD» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FLW_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) (s : riscv_state) :
    Run (instruction.FPLoad (FPLoad.FLW x)) s = «dfn'FLW» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FSD_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) (s : riscv_state) :
    Run (instruction.FPStore (FPStore.FSD x)) s = «dfn'FSD» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_FSW_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) (s : riscv_state) :
    Run (instruction.FPStore (FPStore.FSW x)) s = «dfn'FSW» x s := rfl

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
theorem Run_CSRRC_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) (s : riscv_state) :
    Run (instruction.System (System.CSRRC x)) s = «dfn'CSRRC» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_CSRRCI_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) (s : riscv_state) :
    Run (instruction.System (System.CSRRCI x)) s = «dfn'CSRRCI» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_CSRRS_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) (s : riscv_state) :
    Run (instruction.System (System.CSRRS x)) s = «dfn'CSRRS» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_CSRRSI_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) (s : riscv_state) :
    Run (instruction.System (System.CSRRSI x)) s = «dfn'CSRRSI» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_CSRRW_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) (s : riscv_state) :
    Run (instruction.System (System.CSRRW x)) s = «dfn'CSRRW» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_CSRRWI_equation (x : ((BitVec 5) × ((BitVec 5) × (BitVec 12)))) (s : riscv_state) :
    Run (instruction.System (System.CSRRWI x)) s = «dfn'CSRRWI» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_EBREAK_equation (s : riscv_state) :
    Run (instruction.System (System.EBREAK)) s = «dfn'EBREAK» s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_ECALL_equation (s : riscv_state) :
    Run (instruction.System (System.ECALL)) s = «dfn'ECALL» s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_ERET_equation (s : riscv_state) :
    Run (instruction.System (System.ERET)) s = «dfn'ERET» s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_MRTS_equation (s : riscv_state) :
    Run (instruction.System (System.MRTS)) s = «dfn'MRTS» s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_SFENCE_VM_equation (x : (BitVec 5)) (s : riscv_state) :
    Run (instruction.System (System.SFENCE_VM x)) s = «dfn'SFENCE_VM» x s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_WFI_equation (s : riscv_state) :
    Run (instruction.System (System.WFI)) s = s := rfl

/-- Flapjack kernel check of the complete original dispatch clause; not a separate named HOL theorem. -/
theorem Run_UnknownInstruction_equation (s : riscv_state) :
    Run (instruction.UnknownInstruction) s = «dfn'UnknownInstruction» s := rfl

end Flapjack.RiscV.L3
