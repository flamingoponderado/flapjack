import Flapjack.RiscV.L3.Defs
import Flapjack.Misc.BinaryIeeeDirectedFp32
import Flapjack.Misc.BinaryIeeeDirectedFp64
/-! Original native multiply/add/subtract equations retain separate product
rounding and final sign negation. Symbolic invalid-product cases retain the
original nested choices; no NaN payload is fixed. Numeric state fixtures are
appended from the fresh original capture. docs/SOUNDNESS.md item 8 applies. -/
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 4096
namespace Flapjack.Test.L3RiscvMaddParity
open Flapjack.RiscV.L3 Flapjack
private def state (a b c : BitVec 64) (frm : BitVec 3) : riscv_state :=
  { (default : riscv_state) with
    procID := 7
    c_gpr := fun _ _ => 99
    c_fpr := fun core r => if core = 7 then if r = 1 then a else if r = 2 then b
      else if r = 3 then c else 0xcafe000000000000 else 0xbbbb000000000000
    c_NextFetch := fun _ => none
    c_update := fun _ => { (default : StateDelta) with data1 := some 42 }
    c_UCSR := fun _ => { (default : UserCSR) with
      fpcsr := { (default : FPCSR) with NV := false, NX := true, FRM := frm } }
    c_MCSR := fun _ => { (default : MachineCSR) with
      mstatus := { (default : mstatus) with MFS := 0, MSD := false } } }
private def observe (s : riscv_state) :=
  (FPRD 4 s,FPRD 1 s,FPRD 2 s,FPRD 3 s,(MCSR s).mstatus.MFS,(MCSR s).mstatus.MSD,
    (Delta s).data1,(fcsr s).NV,(fcsr s).NX,s.c_fpr 8 4,
    match NextFetch s with
    | some (.Trap t) => decide (t.trap = ExceptionType.Illegal_Instr ∧ t.badaddr = none)
    | _ => false)

-- Original fmadd_s_invalid_product_rte
example : «dfn'FMADD_S» (4,1,2,3,0) (state 0x0 0x7f800000 0x3f800000 0) =
    writeFPRS (4,(holFloatToFp32 (holFloatAdd .roundTiesToEven (holFp32ToFloat (holFloatToFp32 (holFloatMul .roundTiesToEven (holFp32ToFloat 0x0) (holFp32ToFloat 0x7f800000)).2)) (holFp32ToFloat 0x3f800000)).2)) (state 0x0 0x7f800000 0x3f800000 0) := by rfl

-- Original fmadd_s_invalid_product_rtz
example : «dfn'FMADD_S» (4,1,2,3,1) (state 0x0 0x7f800000 0x3f800000 0) =
    writeFPRS (4,(holFloatToFp32 (holFloatAdd .roundTowardZero (holFp32ToFloat (holFloatToFp32 (holFloatMul .roundTowardZero (holFp32ToFloat 0x0) (holFp32ToFloat 0x7f800000)).2)) (holFp32ToFloat 0x3f800000)).2)) (state 0x0 0x7f800000 0x3f800000 0) := by rfl

-- Original fmadd_s_invalid_product_down
example : «dfn'FMADD_S» (4,1,2,3,2) (state 0x0 0x7f800000 0x3f800000 0) =
    writeFPRS (4,(holFloatToFp32 (holFloatAdd .roundTowardNegative (holFp32ToFloat (holFloatToFp32 (holFloatMul .roundTowardNegative (holFp32ToFloat 0x0) (holFp32ToFloat 0x7f800000)).2)) (holFp32ToFloat 0x3f800000)).2)) (state 0x0 0x7f800000 0x3f800000 0) := by rfl

-- Original fmadd_s_invalid_product_up
example : «dfn'FMADD_S» (4,1,2,3,3) (state 0x0 0x7f800000 0x3f800000 0) =
    writeFPRS (4,(holFloatToFp32 (holFloatAdd .roundTowardPositive (holFp32ToFloat (holFloatToFp32 (holFloatMul .roundTowardPositive (holFp32ToFloat 0x0) (holFp32ToFloat 0x7f800000)).2)) (holFp32ToFloat 0x3f800000)).2)) (state 0x0 0x7f800000 0x3f800000 0) := by rfl

-- Original fmsub_s_invalid_product_rte
example : «dfn'FMSUB_S» (4,1,2,3,0) (state 0x0 0x7f800000 0x3f800000 0) =
    writeFPRS (4,(holFloatToFp32 (holFloatSub .roundTiesToEven (holFp32ToFloat (holFloatToFp32 (holFloatMul .roundTiesToEven (holFp32ToFloat 0x0) (holFp32ToFloat 0x7f800000)).2)) (holFp32ToFloat 0x3f800000)).2)) (state 0x0 0x7f800000 0x3f800000 0) := by rfl

-- Original fmsub_s_invalid_product_rtz
example : «dfn'FMSUB_S» (4,1,2,3,1) (state 0x0 0x7f800000 0x3f800000 0) =
    writeFPRS (4,(holFloatToFp32 (holFloatSub .roundTowardZero (holFp32ToFloat (holFloatToFp32 (holFloatMul .roundTowardZero (holFp32ToFloat 0x0) (holFp32ToFloat 0x7f800000)).2)) (holFp32ToFloat 0x3f800000)).2)) (state 0x0 0x7f800000 0x3f800000 0) := by rfl

-- Original fmsub_s_invalid_product_down
example : «dfn'FMSUB_S» (4,1,2,3,2) (state 0x0 0x7f800000 0x3f800000 0) =
    writeFPRS (4,(holFloatToFp32 (holFloatSub .roundTowardNegative (holFp32ToFloat (holFloatToFp32 (holFloatMul .roundTowardNegative (holFp32ToFloat 0x0) (holFp32ToFloat 0x7f800000)).2)) (holFp32ToFloat 0x3f800000)).2)) (state 0x0 0x7f800000 0x3f800000 0) := by rfl

-- Original fmsub_s_invalid_product_up
example : «dfn'FMSUB_S» (4,1,2,3,3) (state 0x0 0x7f800000 0x3f800000 0) =
    writeFPRS (4,(holFloatToFp32 (holFloatSub .roundTowardPositive (holFp32ToFloat (holFloatToFp32 (holFloatMul .roundTowardPositive (holFp32ToFloat 0x0) (holFp32ToFloat 0x7f800000)).2)) (holFp32ToFloat 0x3f800000)).2)) (state 0x0 0x7f800000 0x3f800000 0) := by rfl

-- Original fnmadd_s_invalid_product_rte
example : «dfn'FNMADD_S» (4,1,2,3,0) (state 0x0 0x7f800000 0x3f800000 0) =
    writeFPRS (4,(holFloatToFp32 (holFloatNegate (holFp32ToFloat (holFloatToFp32 (holFloatAdd .roundTiesToEven (holFp32ToFloat (holFloatToFp32 (holFloatMul .roundTiesToEven (holFp32ToFloat 0x0) (holFp32ToFloat 0x7f800000)).2)) (holFp32ToFloat 0x3f800000)).2))))) (state 0x0 0x7f800000 0x3f800000 0) := by rfl

-- Original fnmadd_s_invalid_product_rtz
example : «dfn'FNMADD_S» (4,1,2,3,1) (state 0x0 0x7f800000 0x3f800000 0) =
    writeFPRS (4,(holFloatToFp32 (holFloatNegate (holFp32ToFloat (holFloatToFp32 (holFloatAdd .roundTowardZero (holFp32ToFloat (holFloatToFp32 (holFloatMul .roundTowardZero (holFp32ToFloat 0x0) (holFp32ToFloat 0x7f800000)).2)) (holFp32ToFloat 0x3f800000)).2))))) (state 0x0 0x7f800000 0x3f800000 0) := by rfl

-- Original fnmadd_s_invalid_product_down
example : «dfn'FNMADD_S» (4,1,2,3,2) (state 0x0 0x7f800000 0x3f800000 0) =
    writeFPRS (4,(holFloatToFp32 (holFloatNegate (holFp32ToFloat (holFloatToFp32 (holFloatAdd .roundTowardNegative (holFp32ToFloat (holFloatToFp32 (holFloatMul .roundTowardNegative (holFp32ToFloat 0x0) (holFp32ToFloat 0x7f800000)).2)) (holFp32ToFloat 0x3f800000)).2))))) (state 0x0 0x7f800000 0x3f800000 0) := by rfl

-- Original fnmadd_s_invalid_product_up
example : «dfn'FNMADD_S» (4,1,2,3,3) (state 0x0 0x7f800000 0x3f800000 0) =
    writeFPRS (4,(holFloatToFp32 (holFloatNegate (holFp32ToFloat (holFloatToFp32 (holFloatAdd .roundTowardPositive (holFp32ToFloat (holFloatToFp32 (holFloatMul .roundTowardPositive (holFp32ToFloat 0x0) (holFp32ToFloat 0x7f800000)).2)) (holFp32ToFloat 0x3f800000)).2))))) (state 0x0 0x7f800000 0x3f800000 0) := by rfl

-- Original fnmsub_s_invalid_product_rte
example : «dfn'FNMSUB_S» (4,1,2,3,0) (state 0x0 0x7f800000 0x3f800000 0) =
    writeFPRS (4,(holFloatToFp32 (holFloatNegate (holFp32ToFloat (holFloatToFp32 (holFloatSub .roundTiesToEven (holFp32ToFloat (holFloatToFp32 (holFloatMul .roundTiesToEven (holFp32ToFloat 0x0) (holFp32ToFloat 0x7f800000)).2)) (holFp32ToFloat 0x3f800000)).2))))) (state 0x0 0x7f800000 0x3f800000 0) := by rfl

-- Original fnmsub_s_invalid_product_rtz
example : «dfn'FNMSUB_S» (4,1,2,3,1) (state 0x0 0x7f800000 0x3f800000 0) =
    writeFPRS (4,(holFloatToFp32 (holFloatNegate (holFp32ToFloat (holFloatToFp32 (holFloatSub .roundTowardZero (holFp32ToFloat (holFloatToFp32 (holFloatMul .roundTowardZero (holFp32ToFloat 0x0) (holFp32ToFloat 0x7f800000)).2)) (holFp32ToFloat 0x3f800000)).2))))) (state 0x0 0x7f800000 0x3f800000 0) := by rfl

-- Original fnmsub_s_invalid_product_down
example : «dfn'FNMSUB_S» (4,1,2,3,2) (state 0x0 0x7f800000 0x3f800000 0) =
    writeFPRS (4,(holFloatToFp32 (holFloatNegate (holFp32ToFloat (holFloatToFp32 (holFloatSub .roundTowardNegative (holFp32ToFloat (holFloatToFp32 (holFloatMul .roundTowardNegative (holFp32ToFloat 0x0) (holFp32ToFloat 0x7f800000)).2)) (holFp32ToFloat 0x3f800000)).2))))) (state 0x0 0x7f800000 0x3f800000 0) := by rfl

-- Original fnmsub_s_invalid_product_up
example : «dfn'FNMSUB_S» (4,1,2,3,3) (state 0x0 0x7f800000 0x3f800000 0) =
    writeFPRS (4,(holFloatToFp32 (holFloatNegate (holFp32ToFloat (holFloatToFp32 (holFloatSub .roundTowardPositive (holFp32ToFloat (holFloatToFp32 (holFloatMul .roundTowardPositive (holFp32ToFloat 0x0) (holFp32ToFloat 0x7f800000)).2)) (holFp32ToFloat 0x3f800000)).2))))) (state 0x0 0x7f800000 0x3f800000 0) := by rfl

-- Original fmadd_d_invalid_product_rte
example : «dfn'FMADD_D» (4,1,2,3,0) (state 0x0 0x7ff0000000000000 0x3ff0000000000000 0) =
    writeFPRD (4,(holFloatToFp64 (holFloatAdd .roundTiesToEven (holFp64ToFloat (holFloatToFp64 (holFloatMul .roundTiesToEven (holFp64ToFloat 0x0) (holFp64ToFloat 0x7ff0000000000000)).2)) (holFp64ToFloat 0x3ff0000000000000)).2)) (state 0x0 0x7ff0000000000000 0x3ff0000000000000 0) := by rfl

-- Original fmadd_d_invalid_product_rtz
example : «dfn'FMADD_D» (4,1,2,3,1) (state 0x0 0x7ff0000000000000 0x3ff0000000000000 0) =
    writeFPRD (4,(holFloatToFp64 (holFloatAdd .roundTowardZero (holFp64ToFloat (holFloatToFp64 (holFloatMul .roundTowardZero (holFp64ToFloat 0x0) (holFp64ToFloat 0x7ff0000000000000)).2)) (holFp64ToFloat 0x3ff0000000000000)).2)) (state 0x0 0x7ff0000000000000 0x3ff0000000000000 0) := by rfl

-- Original fmadd_d_invalid_product_down
example : «dfn'FMADD_D» (4,1,2,3,2) (state 0x0 0x7ff0000000000000 0x3ff0000000000000 0) =
    writeFPRD (4,(holFloatToFp64 (holFloatAdd .roundTowardNegative (holFp64ToFloat (holFloatToFp64 (holFloatMul .roundTowardNegative (holFp64ToFloat 0x0) (holFp64ToFloat 0x7ff0000000000000)).2)) (holFp64ToFloat 0x3ff0000000000000)).2)) (state 0x0 0x7ff0000000000000 0x3ff0000000000000 0) := by rfl

-- Original fmadd_d_invalid_product_up
example : «dfn'FMADD_D» (4,1,2,3,3) (state 0x0 0x7ff0000000000000 0x3ff0000000000000 0) =
    writeFPRD (4,(holFloatToFp64 (holFloatAdd .roundTowardPositive (holFp64ToFloat (holFloatToFp64 (holFloatMul .roundTowardPositive (holFp64ToFloat 0x0) (holFp64ToFloat 0x7ff0000000000000)).2)) (holFp64ToFloat 0x3ff0000000000000)).2)) (state 0x0 0x7ff0000000000000 0x3ff0000000000000 0) := by rfl

-- Original fmsub_d_invalid_product_rte
example : «dfn'FMSUB_D» (4,1,2,3,0) (state 0x0 0x7ff0000000000000 0x3ff0000000000000 0) =
    writeFPRD (4,(holFloatToFp64 (holFloatSub .roundTiesToEven (holFp64ToFloat (holFloatToFp64 (holFloatMul .roundTiesToEven (holFp64ToFloat 0x0) (holFp64ToFloat 0x7ff0000000000000)).2)) (holFp64ToFloat 0x3ff0000000000000)).2)) (state 0x0 0x7ff0000000000000 0x3ff0000000000000 0) := by rfl

-- Original fmsub_d_invalid_product_rtz
example : «dfn'FMSUB_D» (4,1,2,3,1) (state 0x0 0x7ff0000000000000 0x3ff0000000000000 0) =
    writeFPRD (4,(holFloatToFp64 (holFloatSub .roundTowardZero (holFp64ToFloat (holFloatToFp64 (holFloatMul .roundTowardZero (holFp64ToFloat 0x0) (holFp64ToFloat 0x7ff0000000000000)).2)) (holFp64ToFloat 0x3ff0000000000000)).2)) (state 0x0 0x7ff0000000000000 0x3ff0000000000000 0) := by rfl

-- Original fmsub_d_invalid_product_down
example : «dfn'FMSUB_D» (4,1,2,3,2) (state 0x0 0x7ff0000000000000 0x3ff0000000000000 0) =
    writeFPRD (4,(holFloatToFp64 (holFloatSub .roundTowardNegative (holFp64ToFloat (holFloatToFp64 (holFloatMul .roundTowardNegative (holFp64ToFloat 0x0) (holFp64ToFloat 0x7ff0000000000000)).2)) (holFp64ToFloat 0x3ff0000000000000)).2)) (state 0x0 0x7ff0000000000000 0x3ff0000000000000 0) := by rfl

-- Original fmsub_d_invalid_product_up
example : «dfn'FMSUB_D» (4,1,2,3,3) (state 0x0 0x7ff0000000000000 0x3ff0000000000000 0) =
    writeFPRD (4,(holFloatToFp64 (holFloatSub .roundTowardPositive (holFp64ToFloat (holFloatToFp64 (holFloatMul .roundTowardPositive (holFp64ToFloat 0x0) (holFp64ToFloat 0x7ff0000000000000)).2)) (holFp64ToFloat 0x3ff0000000000000)).2)) (state 0x0 0x7ff0000000000000 0x3ff0000000000000 0) := by rfl

-- Original fnmadd_d_invalid_product_rte
example : «dfn'FNMADD_D» (4,1,2,3,0) (state 0x0 0x7ff0000000000000 0x3ff0000000000000 0) =
    writeFPRD (4,(holFloatToFp64 (holFloatNegate (holFp64ToFloat (holFloatToFp64 (holFloatAdd .roundTiesToEven (holFp64ToFloat (holFloatToFp64 (holFloatMul .roundTiesToEven (holFp64ToFloat 0x0) (holFp64ToFloat 0x7ff0000000000000)).2)) (holFp64ToFloat 0x3ff0000000000000)).2))))) (state 0x0 0x7ff0000000000000 0x3ff0000000000000 0) := by rfl

-- Original fnmadd_d_invalid_product_rtz
example : «dfn'FNMADD_D» (4,1,2,3,1) (state 0x0 0x7ff0000000000000 0x3ff0000000000000 0) =
    writeFPRD (4,(holFloatToFp64 (holFloatNegate (holFp64ToFloat (holFloatToFp64 (holFloatAdd .roundTowardZero (holFp64ToFloat (holFloatToFp64 (holFloatMul .roundTowardZero (holFp64ToFloat 0x0) (holFp64ToFloat 0x7ff0000000000000)).2)) (holFp64ToFloat 0x3ff0000000000000)).2))))) (state 0x0 0x7ff0000000000000 0x3ff0000000000000 0) := by rfl

-- Original fnmadd_d_invalid_product_down
example : «dfn'FNMADD_D» (4,1,2,3,2) (state 0x0 0x7ff0000000000000 0x3ff0000000000000 0) =
    writeFPRD (4,(holFloatToFp64 (holFloatNegate (holFp64ToFloat (holFloatToFp64 (holFloatAdd .roundTowardNegative (holFp64ToFloat (holFloatToFp64 (holFloatMul .roundTowardNegative (holFp64ToFloat 0x0) (holFp64ToFloat 0x7ff0000000000000)).2)) (holFp64ToFloat 0x3ff0000000000000)).2))))) (state 0x0 0x7ff0000000000000 0x3ff0000000000000 0) := by rfl

-- Original fnmadd_d_invalid_product_up
example : «dfn'FNMADD_D» (4,1,2,3,3) (state 0x0 0x7ff0000000000000 0x3ff0000000000000 0) =
    writeFPRD (4,(holFloatToFp64 (holFloatNegate (holFp64ToFloat (holFloatToFp64 (holFloatAdd .roundTowardPositive (holFp64ToFloat (holFloatToFp64 (holFloatMul .roundTowardPositive (holFp64ToFloat 0x0) (holFp64ToFloat 0x7ff0000000000000)).2)) (holFp64ToFloat 0x3ff0000000000000)).2))))) (state 0x0 0x7ff0000000000000 0x3ff0000000000000 0) := by rfl

-- Original fnmsub_d_invalid_product_rte
example : «dfn'FNMSUB_D» (4,1,2,3,0) (state 0x0 0x7ff0000000000000 0x3ff0000000000000 0) =
    writeFPRD (4,(holFloatToFp64 (holFloatNegate (holFp64ToFloat (holFloatToFp64 (holFloatSub .roundTiesToEven (holFp64ToFloat (holFloatToFp64 (holFloatMul .roundTiesToEven (holFp64ToFloat 0x0) (holFp64ToFloat 0x7ff0000000000000)).2)) (holFp64ToFloat 0x3ff0000000000000)).2))))) (state 0x0 0x7ff0000000000000 0x3ff0000000000000 0) := by rfl

-- Original fnmsub_d_invalid_product_rtz
example : «dfn'FNMSUB_D» (4,1,2,3,1) (state 0x0 0x7ff0000000000000 0x3ff0000000000000 0) =
    writeFPRD (4,(holFloatToFp64 (holFloatNegate (holFp64ToFloat (holFloatToFp64 (holFloatSub .roundTowardZero (holFp64ToFloat (holFloatToFp64 (holFloatMul .roundTowardZero (holFp64ToFloat 0x0) (holFp64ToFloat 0x7ff0000000000000)).2)) (holFp64ToFloat 0x3ff0000000000000)).2))))) (state 0x0 0x7ff0000000000000 0x3ff0000000000000 0) := by rfl

-- Original fnmsub_d_invalid_product_down
example : «dfn'FNMSUB_D» (4,1,2,3,2) (state 0x0 0x7ff0000000000000 0x3ff0000000000000 0) =
    writeFPRD (4,(holFloatToFp64 (holFloatNegate (holFp64ToFloat (holFloatToFp64 (holFloatSub .roundTowardNegative (holFp64ToFloat (holFloatToFp64 (holFloatMul .roundTowardNegative (holFp64ToFloat 0x0) (holFp64ToFloat 0x7ff0000000000000)).2)) (holFp64ToFloat 0x3ff0000000000000)).2))))) (state 0x0 0x7ff0000000000000 0x3ff0000000000000 0) := by rfl

-- Original fnmsub_d_invalid_product_up
example : «dfn'FNMSUB_D» (4,1,2,3,3) (state 0x0 0x7ff0000000000000 0x3ff0000000000000 0) =
    writeFPRD (4,(holFloatToFp64 (holFloatNegate (holFp64ToFloat (holFloatToFp64 (holFloatSub .roundTowardPositive (holFp64ToFloat (holFloatToFp64 (holFloatMul .roundTowardPositive (holFp64ToFloat 0x0) (holFp64ToFloat 0x7ff0000000000000)).2)) (holFp64ToFloat 0x3ff0000000000000)).2))))) (state 0x0 0x7ff0000000000000 0x3ff0000000000000 0) := by rfl


-- Original fmadd_s_basic_rte
example : observe («dfn'FMADD_S» (4,1,2,3,0) (state 0x3f800000 0x40000000 0x40400000 0)) =
    (0xCAFE000040A00000,0x3F800000,0x40000000,0x40400000,3,true,
 (some 0x40A00000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmadd_s_basic_rtz
example : observe («dfn'FMADD_S» (4,1,2,3,1) (state 0x3f800000 0x40000000 0x40400000 0)) =
    (0xCAFE000040A00000,0x3F800000,0x40000000,0x40400000,3,true,
 (some 0x40A00000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmadd_s_basic_down
example : observe («dfn'FMADD_S» (4,1,2,3,2) (state 0x3f800000 0x40000000 0x40400000 0)) =
    (0xCAFE000040A00000,0x3F800000,0x40000000,0x40400000,3,true,
 (some 0x40A00000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmadd_s_basic_up
example : observe («dfn'FMADD_S» (4,1,2,3,3) (state 0x3f800000 0x40000000 0x40400000 0)) =
    (0xCAFE000040A00000,0x3F800000,0x40000000,0x40400000,3,true,
 (some 0x40A00000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmadd_s_basic_dynamic_up
example : observe («dfn'FMADD_S» (4,1,2,3,7) (state 0x3f800000 0x40000000 0x40400000 3)) =
    (0xCAFE000040A00000,0x3F800000,0x40000000,0x40400000,3,true,
 (some 0x40A00000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmadd_s_basic_invalid_static
example : observe («dfn'FMADD_S» (4,1,2,3,4) (state 0x3f800000 0x40000000 0x40400000 0)) =
    (0xCAFE000000000000,0x3F800000,0x40000000,0x40400000,0,false,(some 42),false,true,
 0xBBBB000000000000,true) := by
  simp only [«dfn'FMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmadd_s_basic_invalid_dynamic
example : observe («dfn'FMADD_S» (4,1,2,3,7) (state 0x3f800000 0x40000000 0x40400000 4)) =
    (0xCAFE000000000000,0x3F800000,0x40000000,0x40400000,0,false,(some 42),false,true,
 0xBBBB000000000000,true) := by
  simp only [«dfn'FMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmadd_s_double_round_rte
example : observe («dfn'FMADD_S» (4,1,2,3,0) (state 0x3f800001 0x3f7ffffe 0xbf800000 0)) =
    (0xCAFE000000000000,0x3F800001,0x3F7FFFFE,0xBF800000,3,true,(some 0),false,true,
 0xBBBB000000000000,false) := by
  simp only [«dfn'FMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmadd_s_double_round_rtz
example : observe («dfn'FMADD_S» (4,1,2,3,1) (state 0x3f800001 0x3f7ffffe 0xbf800000 0)) =
    (0xCAFE0000B3800000,0x3F800001,0x3F7FFFFE,0xBF800000,3,true,
 (some 0xB3800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmadd_s_double_round_down
example : observe («dfn'FMADD_S» (4,1,2,3,2) (state 0x3f800001 0x3f7ffffe 0xbf800000 0)) =
    (0xCAFE0000B3800000,0x3F800001,0x3F7FFFFE,0xBF800000,3,true,
 (some 0xB3800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmadd_s_double_round_up
example : observe («dfn'FMADD_S» (4,1,2,3,3) (state 0x3f800001 0x3f7ffffe 0xbf800000 0)) =
    (0xCAFE000000000000,0x3F800001,0x3F7FFFFE,0xBF800000,3,true,(some 0),false,true,
 0xBBBB000000000000,false) := by
  simp only [«dfn'FMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmadd_s_double_round_dynamic_up
example : observe («dfn'FMADD_S» (4,1,2,3,7) (state 0x3f800001 0x3f7ffffe 0xbf800000 3)) =
    (0xCAFE000000000000,0x3F800001,0x3F7FFFFE,0xBF800000,3,true,(some 0),false,true,
 0xBBBB000000000000,false) := by
  simp only [«dfn'FMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmadd_s_double_round_invalid_static
example : observe («dfn'FMADD_S» (4,1,2,3,4) (state 0x3f800001 0x3f7ffffe 0xbf800000 0)) =
    (0xCAFE000000000000,0x3F800001,0x3F7FFFFE,0xBF800000,0,false,(some 42),false,true,
 0xBBBB000000000000,true) := by
  simp only [«dfn'FMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmadd_s_double_round_invalid_dynamic
example : observe («dfn'FMADD_S» (4,1,2,3,7) (state 0x3f800001 0x3f7ffffe 0xbf800000 4)) =
    (0xCAFE000000000000,0x3F800001,0x3F7FFFFE,0xBF800000,0,false,(some 42),false,true,
 0xBBBB000000000000,true) := by
  simp only [«dfn'FMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmadd_s_signed_zero_rte
example : observe («dfn'FMADD_S» (4,1,2,3,0) (state 0x80000000 0x40000000 0x0 0)) =
    (0xCAFE000000000000,0x80000000,0x40000000,0,3,true,(some 0),false,true,
 0xBBBB000000000000,false) := by
  simp only [«dfn'FMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmadd_s_signed_zero_rtz
example : observe («dfn'FMADD_S» (4,1,2,3,1) (state 0x80000000 0x40000000 0x0 0)) =
    (0xCAFE000000000000,0x80000000,0x40000000,0,3,true,(some 0),false,true,
 0xBBBB000000000000,false) := by
  simp only [«dfn'FMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmadd_s_signed_zero_down
example : observe («dfn'FMADD_S» (4,1,2,3,2) (state 0x80000000 0x40000000 0x0 0)) =
    (0xCAFE000080000000,0x80000000,0x40000000,0,3,true,(some 0x80000000),false,true,
 0xBBBB000000000000,false) := by
  simp only [«dfn'FMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmadd_s_signed_zero_up
example : observe («dfn'FMADD_S» (4,1,2,3,3) (state 0x80000000 0x40000000 0x0 0)) =
    (0xCAFE000000000000,0x80000000,0x40000000,0,3,true,(some 0),false,true,
 0xBBBB000000000000,false) := by
  simp only [«dfn'FMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmadd_s_infinity_rte
example : observe («dfn'FMADD_S» (4,1,2,3,0) (state 0x7f800000 0xbf800000 0x3f800000 0)) =
    (0xCAFE0000FF800000,0x7F800000,0xBF800000,0x3F800000,3,true,
 (some 0xFF800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmadd_s_infinity_rtz
example : observe («dfn'FMADD_S» (4,1,2,3,1) (state 0x7f800000 0xbf800000 0x3f800000 0)) =
    (0xCAFE0000FF800000,0x7F800000,0xBF800000,0x3F800000,3,true,
 (some 0xFF800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmadd_s_infinity_down
example : observe («dfn'FMADD_S» (4,1,2,3,2) (state 0x7f800000 0xbf800000 0x3f800000 0)) =
    (0xCAFE0000FF800000,0x7F800000,0xBF800000,0x3F800000,3,true,
 (some 0xFF800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmadd_s_infinity_up
example : observe («dfn'FMADD_S» (4,1,2,3,3) (state 0x7f800000 0xbf800000 0x3f800000 0)) =
    (0xCAFE0000FF800000,0x7F800000,0xBF800000,0x3F800000,3,true,
 (some 0xFF800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmadd_s_negative_finite_rte
example : observe («dfn'FMADD_S» (4,1,2,3,0) (state 0xbf800000 0x40000000 0x40400000 0)) =
    (0xCAFE00003F800000,0xBF800000,0x40000000,0x40400000,3,true,
 (some 0x3F800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmadd_s_negative_finite_rtz
example : observe («dfn'FMADD_S» (4,1,2,3,1) (state 0xbf800000 0x40000000 0x40400000 0)) =
    (0xCAFE00003F800000,0xBF800000,0x40000000,0x40400000,3,true,
 (some 0x3F800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmadd_s_negative_finite_down
example : observe («dfn'FMADD_S» (4,1,2,3,2) (state 0xbf800000 0x40000000 0x40400000 0)) =
    (0xCAFE00003F800000,0xBF800000,0x40000000,0x40400000,3,true,
 (some 0x3F800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmadd_s_negative_finite_up
example : observe («dfn'FMADD_S» (4,1,2,3,3) (state 0xbf800000 0x40000000 0x40400000 0)) =
    (0xCAFE00003F800000,0xBF800000,0x40000000,0x40400000,3,true,
 (some 0x3F800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmsub_s_basic_rte
example : observe («dfn'FMSUB_S» (4,1,2,3,0) (state 0x3f800000 0x40000000 0x40400000 0)) =
    (0xCAFE0000BF800000,0x3F800000,0x40000000,0x40400000,3,true,
 (some 0xBF800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmsub_s_basic_rtz
example : observe («dfn'FMSUB_S» (4,1,2,3,1) (state 0x3f800000 0x40000000 0x40400000 0)) =
    (0xCAFE0000BF800000,0x3F800000,0x40000000,0x40400000,3,true,
 (some 0xBF800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmsub_s_basic_down
example : observe («dfn'FMSUB_S» (4,1,2,3,2) (state 0x3f800000 0x40000000 0x40400000 0)) =
    (0xCAFE0000BF800000,0x3F800000,0x40000000,0x40400000,3,true,
 (some 0xBF800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmsub_s_basic_up
example : observe («dfn'FMSUB_S» (4,1,2,3,3) (state 0x3f800000 0x40000000 0x40400000 0)) =
    (0xCAFE0000BF800000,0x3F800000,0x40000000,0x40400000,3,true,
 (some 0xBF800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmsub_s_basic_dynamic_up
example : observe («dfn'FMSUB_S» (4,1,2,3,7) (state 0x3f800000 0x40000000 0x40400000 3)) =
    (0xCAFE0000BF800000,0x3F800000,0x40000000,0x40400000,3,true,
 (some 0xBF800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmsub_s_basic_invalid_static
example : observe («dfn'FMSUB_S» (4,1,2,3,4) (state 0x3f800000 0x40000000 0x40400000 0)) =
    (0xCAFE000000000000,0x3F800000,0x40000000,0x40400000,0,false,(some 42),false,true,
 0xBBBB000000000000,true) := by
  simp only [«dfn'FMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmsub_s_basic_invalid_dynamic
example : observe («dfn'FMSUB_S» (4,1,2,3,7) (state 0x3f800000 0x40000000 0x40400000 4)) =
    (0xCAFE000000000000,0x3F800000,0x40000000,0x40400000,0,false,(some 42),false,true,
 0xBBBB000000000000,true) := by
  simp only [«dfn'FMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmsub_s_double_round_rte
example : observe («dfn'FMSUB_S» (4,1,2,3,0) (state 0x3f800001 0x3f7ffffe 0x3f800000 0)) =
    (0xCAFE000000000000,0x3F800001,0x3F7FFFFE,0x3F800000,3,true,(some 0),false,true,
 0xBBBB000000000000,false) := by
  simp only [«dfn'FMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmsub_s_double_round_rtz
example : observe («dfn'FMSUB_S» (4,1,2,3,1) (state 0x3f800001 0x3f7ffffe 0x3f800000 0)) =
    (0xCAFE0000B3800000,0x3F800001,0x3F7FFFFE,0x3F800000,3,true,
 (some 0xB3800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmsub_s_double_round_down
example : observe («dfn'FMSUB_S» (4,1,2,3,2) (state 0x3f800001 0x3f7ffffe 0x3f800000 0)) =
    (0xCAFE0000B3800000,0x3F800001,0x3F7FFFFE,0x3F800000,3,true,
 (some 0xB3800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmsub_s_double_round_up
example : observe («dfn'FMSUB_S» (4,1,2,3,3) (state 0x3f800001 0x3f7ffffe 0x3f800000 0)) =
    (0xCAFE000000000000,0x3F800001,0x3F7FFFFE,0x3F800000,3,true,(some 0),false,true,
 0xBBBB000000000000,false) := by
  simp only [«dfn'FMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmsub_s_double_round_dynamic_up
example : observe («dfn'FMSUB_S» (4,1,2,3,7) (state 0x3f800001 0x3f7ffffe 0x3f800000 3)) =
    (0xCAFE000000000000,0x3F800001,0x3F7FFFFE,0x3F800000,3,true,(some 0),false,true,
 0xBBBB000000000000,false) := by
  simp only [«dfn'FMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmsub_s_double_round_invalid_static
example : observe («dfn'FMSUB_S» (4,1,2,3,4) (state 0x3f800001 0x3f7ffffe 0x3f800000 0)) =
    (0xCAFE000000000000,0x3F800001,0x3F7FFFFE,0x3F800000,0,false,(some 42),false,true,
 0xBBBB000000000000,true) := by
  simp only [«dfn'FMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmsub_s_double_round_invalid_dynamic
example : observe («dfn'FMSUB_S» (4,1,2,3,7) (state 0x3f800001 0x3f7ffffe 0x3f800000 4)) =
    (0xCAFE000000000000,0x3F800001,0x3F7FFFFE,0x3F800000,0,false,(some 42),false,true,
 0xBBBB000000000000,true) := by
  simp only [«dfn'FMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmsub_s_signed_zero_rte
example : observe («dfn'FMSUB_S» (4,1,2,3,0) (state 0x80000000 0x40000000 0x0 0)) =
    (0xCAFE000080000000,0x80000000,0x40000000,0,3,true,(some 0x80000000),false,true,
 0xBBBB000000000000,false) := by
  simp only [«dfn'FMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmsub_s_signed_zero_rtz
example : observe («dfn'FMSUB_S» (4,1,2,3,1) (state 0x80000000 0x40000000 0x0 0)) =
    (0xCAFE000080000000,0x80000000,0x40000000,0,3,true,(some 0x80000000),false,true,
 0xBBBB000000000000,false) := by
  simp only [«dfn'FMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmsub_s_signed_zero_down
example : observe («dfn'FMSUB_S» (4,1,2,3,2) (state 0x80000000 0x40000000 0x0 0)) =
    (0xCAFE000080000000,0x80000000,0x40000000,0,3,true,(some 0x80000000),false,true,
 0xBBBB000000000000,false) := by
  simp only [«dfn'FMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmsub_s_signed_zero_up
example : observe («dfn'FMSUB_S» (4,1,2,3,3) (state 0x80000000 0x40000000 0x0 0)) =
    (0xCAFE000080000000,0x80000000,0x40000000,0,3,true,(some 0x80000000),false,true,
 0xBBBB000000000000,false) := by
  simp only [«dfn'FMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmsub_s_infinity_rte
example : observe («dfn'FMSUB_S» (4,1,2,3,0) (state 0x7f800000 0xbf800000 0x3f800000 0)) =
    (0xCAFE0000FF800000,0x7F800000,0xBF800000,0x3F800000,3,true,
 (some 0xFF800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmsub_s_infinity_rtz
example : observe («dfn'FMSUB_S» (4,1,2,3,1) (state 0x7f800000 0xbf800000 0x3f800000 0)) =
    (0xCAFE0000FF800000,0x7F800000,0xBF800000,0x3F800000,3,true,
 (some 0xFF800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmsub_s_infinity_down
example : observe («dfn'FMSUB_S» (4,1,2,3,2) (state 0x7f800000 0xbf800000 0x3f800000 0)) =
    (0xCAFE0000FF800000,0x7F800000,0xBF800000,0x3F800000,3,true,
 (some 0xFF800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmsub_s_infinity_up
example : observe («dfn'FMSUB_S» (4,1,2,3,3) (state 0x7f800000 0xbf800000 0x3f800000 0)) =
    (0xCAFE0000FF800000,0x7F800000,0xBF800000,0x3F800000,3,true,
 (some 0xFF800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmsub_s_negative_finite_rte
example : observe («dfn'FMSUB_S» (4,1,2,3,0) (state 0xbf800000 0x40000000 0x40400000 0)) =
    (0xCAFE0000C0A00000,0xBF800000,0x40000000,0x40400000,3,true,
 (some 0xC0A00000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmsub_s_negative_finite_rtz
example : observe («dfn'FMSUB_S» (4,1,2,3,1) (state 0xbf800000 0x40000000 0x40400000 0)) =
    (0xCAFE0000C0A00000,0xBF800000,0x40000000,0x40400000,3,true,
 (some 0xC0A00000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmsub_s_negative_finite_down
example : observe («dfn'FMSUB_S» (4,1,2,3,2) (state 0xbf800000 0x40000000 0x40400000 0)) =
    (0xCAFE0000C0A00000,0xBF800000,0x40000000,0x40400000,3,true,
 (some 0xC0A00000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmsub_s_negative_finite_up
example : observe («dfn'FMSUB_S» (4,1,2,3,3) (state 0xbf800000 0x40000000 0x40400000 0)) =
    (0xCAFE0000C0A00000,0xBF800000,0x40000000,0x40400000,3,true,
 (some 0xC0A00000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmadd_s_basic_rte
example : observe («dfn'FNMADD_S» (4,1,2,3,0) (state 0x3f800000 0x40000000 0x40400000 0)) =
    (0xCAFE0000C0A00000,0x3F800000,0x40000000,0x40400000,3,true,
 (some 0xC0A00000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmadd_s_basic_rtz
example : observe («dfn'FNMADD_S» (4,1,2,3,1) (state 0x3f800000 0x40000000 0x40400000 0)) =
    (0xCAFE0000C0A00000,0x3F800000,0x40000000,0x40400000,3,true,
 (some 0xC0A00000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmadd_s_basic_down
example : observe («dfn'FNMADD_S» (4,1,2,3,2) (state 0x3f800000 0x40000000 0x40400000 0)) =
    (0xCAFE0000C0A00000,0x3F800000,0x40000000,0x40400000,3,true,
 (some 0xC0A00000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmadd_s_basic_up
example : observe («dfn'FNMADD_S» (4,1,2,3,3) (state 0x3f800000 0x40000000 0x40400000 0)) =
    (0xCAFE0000C0A00000,0x3F800000,0x40000000,0x40400000,3,true,
 (some 0xC0A00000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmadd_s_basic_dynamic_up
example : observe («dfn'FNMADD_S» (4,1,2,3,7) (state 0x3f800000 0x40000000 0x40400000 3)) =
    (0xCAFE0000C0A00000,0x3F800000,0x40000000,0x40400000,3,true,
 (some 0xC0A00000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmadd_s_basic_invalid_static
example : observe («dfn'FNMADD_S» (4,1,2,3,4) (state 0x3f800000 0x40000000 0x40400000 0)) =
    (0xCAFE000000000000,0x3F800000,0x40000000,0x40400000,0,false,(some 42),false,true,
 0xBBBB000000000000,true) := by
  simp only [«dfn'FNMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmadd_s_basic_invalid_dynamic
example : observe («dfn'FNMADD_S» (4,1,2,3,7) (state 0x3f800000 0x40000000 0x40400000 4)) =
    (0xCAFE000000000000,0x3F800000,0x40000000,0x40400000,0,false,(some 42),false,true,
 0xBBBB000000000000,true) := by
  simp only [«dfn'FNMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmadd_s_double_round_rte
example : observe («dfn'FNMADD_S» (4,1,2,3,0) (state 0x3f800001 0x3f7ffffe 0xbf800000 0)) =
    (0xCAFE000080000000,0x3F800001,0x3F7FFFFE,0xBF800000,3,true,
 (some 0x80000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmadd_s_double_round_rtz
example : observe («dfn'FNMADD_S» (4,1,2,3,1) (state 0x3f800001 0x3f7ffffe 0xbf800000 0)) =
    (0xCAFE000033800000,0x3F800001,0x3F7FFFFE,0xBF800000,3,true,
 (some 0x33800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmadd_s_double_round_down
example : observe («dfn'FNMADD_S» (4,1,2,3,2) (state 0x3f800001 0x3f7ffffe 0xbf800000 0)) =
    (0xCAFE000033800000,0x3F800001,0x3F7FFFFE,0xBF800000,3,true,
 (some 0x33800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmadd_s_double_round_up
example : observe («dfn'FNMADD_S» (4,1,2,3,3) (state 0x3f800001 0x3f7ffffe 0xbf800000 0)) =
    (0xCAFE000080000000,0x3F800001,0x3F7FFFFE,0xBF800000,3,true,
 (some 0x80000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmadd_s_double_round_dynamic_up
example : observe («dfn'FNMADD_S» (4,1,2,3,7) (state 0x3f800001 0x3f7ffffe 0xbf800000 3)) =
    (0xCAFE000080000000,0x3F800001,0x3F7FFFFE,0xBF800000,3,true,
 (some 0x80000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmadd_s_double_round_invalid_static
example : observe («dfn'FNMADD_S» (4,1,2,3,4) (state 0x3f800001 0x3f7ffffe 0xbf800000 0)) =
    (0xCAFE000000000000,0x3F800001,0x3F7FFFFE,0xBF800000,0,false,(some 42),false,true,
 0xBBBB000000000000,true) := by
  simp only [«dfn'FNMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmadd_s_double_round_invalid_dynamic
example : observe («dfn'FNMADD_S» (4,1,2,3,7) (state 0x3f800001 0x3f7ffffe 0xbf800000 4)) =
    (0xCAFE000000000000,0x3F800001,0x3F7FFFFE,0xBF800000,0,false,(some 42),false,true,
 0xBBBB000000000000,true) := by
  simp only [«dfn'FNMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmadd_s_signed_zero_rte
example : observe («dfn'FNMADD_S» (4,1,2,3,0) (state 0x80000000 0x40000000 0x0 0)) =
    (0xCAFE000080000000,0x80000000,0x40000000,0,3,true,(some 0x80000000),false,true,
 0xBBBB000000000000,false) := by
  simp only [«dfn'FNMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmadd_s_signed_zero_rtz
example : observe («dfn'FNMADD_S» (4,1,2,3,1) (state 0x80000000 0x40000000 0x0 0)) =
    (0xCAFE000080000000,0x80000000,0x40000000,0,3,true,(some 0x80000000),false,true,
 0xBBBB000000000000,false) := by
  simp only [«dfn'FNMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmadd_s_signed_zero_down
example : observe («dfn'FNMADD_S» (4,1,2,3,2) (state 0x80000000 0x40000000 0x0 0)) =
    (0xCAFE000000000000,0x80000000,0x40000000,0,3,true,(some 0),false,true,
 0xBBBB000000000000,false) := by
  simp only [«dfn'FNMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmadd_s_signed_zero_up
example : observe («dfn'FNMADD_S» (4,1,2,3,3) (state 0x80000000 0x40000000 0x0 0)) =
    (0xCAFE000080000000,0x80000000,0x40000000,0,3,true,(some 0x80000000),false,true,
 0xBBBB000000000000,false) := by
  simp only [«dfn'FNMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmadd_s_infinity_rte
example : observe («dfn'FNMADD_S» (4,1,2,3,0) (state 0x7f800000 0xbf800000 0x3f800000 0)) =
    (0xCAFE00007F800000,0x7F800000,0xBF800000,0x3F800000,3,true,
 (some 0x7F800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmadd_s_infinity_rtz
example : observe («dfn'FNMADD_S» (4,1,2,3,1) (state 0x7f800000 0xbf800000 0x3f800000 0)) =
    (0xCAFE00007F800000,0x7F800000,0xBF800000,0x3F800000,3,true,
 (some 0x7F800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmadd_s_infinity_down
example : observe («dfn'FNMADD_S» (4,1,2,3,2) (state 0x7f800000 0xbf800000 0x3f800000 0)) =
    (0xCAFE00007F800000,0x7F800000,0xBF800000,0x3F800000,3,true,
 (some 0x7F800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmadd_s_infinity_up
example : observe («dfn'FNMADD_S» (4,1,2,3,3) (state 0x7f800000 0xbf800000 0x3f800000 0)) =
    (0xCAFE00007F800000,0x7F800000,0xBF800000,0x3F800000,3,true,
 (some 0x7F800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmadd_s_negative_finite_rte
example : observe («dfn'FNMADD_S» (4,1,2,3,0) (state 0xbf800000 0x40000000 0x40400000 0)) =
    (0xCAFE0000BF800000,0xBF800000,0x40000000,0x40400000,3,true,
 (some 0xBF800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmadd_s_negative_finite_rtz
example : observe («dfn'FNMADD_S» (4,1,2,3,1) (state 0xbf800000 0x40000000 0x40400000 0)) =
    (0xCAFE0000BF800000,0xBF800000,0x40000000,0x40400000,3,true,
 (some 0xBF800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmadd_s_negative_finite_down
example : observe («dfn'FNMADD_S» (4,1,2,3,2) (state 0xbf800000 0x40000000 0x40400000 0)) =
    (0xCAFE0000BF800000,0xBF800000,0x40000000,0x40400000,3,true,
 (some 0xBF800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmadd_s_negative_finite_up
example : observe («dfn'FNMADD_S» (4,1,2,3,3) (state 0xbf800000 0x40000000 0x40400000 0)) =
    (0xCAFE0000BF800000,0xBF800000,0x40000000,0x40400000,3,true,
 (some 0xBF800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMADD_S», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmsub_s_basic_rte
example : observe («dfn'FNMSUB_S» (4,1,2,3,0) (state 0x3f800000 0x40000000 0x40400000 0)) =
    (0xCAFE00003F800000,0x3F800000,0x40000000,0x40400000,3,true,
 (some 0x3F800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmsub_s_basic_rtz
example : observe («dfn'FNMSUB_S» (4,1,2,3,1) (state 0x3f800000 0x40000000 0x40400000 0)) =
    (0xCAFE00003F800000,0x3F800000,0x40000000,0x40400000,3,true,
 (some 0x3F800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmsub_s_basic_down
example : observe («dfn'FNMSUB_S» (4,1,2,3,2) (state 0x3f800000 0x40000000 0x40400000 0)) =
    (0xCAFE00003F800000,0x3F800000,0x40000000,0x40400000,3,true,
 (some 0x3F800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmsub_s_basic_up
example : observe («dfn'FNMSUB_S» (4,1,2,3,3) (state 0x3f800000 0x40000000 0x40400000 0)) =
    (0xCAFE00003F800000,0x3F800000,0x40000000,0x40400000,3,true,
 (some 0x3F800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmsub_s_basic_dynamic_up
example : observe («dfn'FNMSUB_S» (4,1,2,3,7) (state 0x3f800000 0x40000000 0x40400000 3)) =
    (0xCAFE00003F800000,0x3F800000,0x40000000,0x40400000,3,true,
 (some 0x3F800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmsub_s_basic_invalid_static
example : observe («dfn'FNMSUB_S» (4,1,2,3,4) (state 0x3f800000 0x40000000 0x40400000 0)) =
    (0xCAFE000000000000,0x3F800000,0x40000000,0x40400000,0,false,(some 42),false,true,
 0xBBBB000000000000,true) := by
  simp only [«dfn'FNMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmsub_s_basic_invalid_dynamic
example : observe («dfn'FNMSUB_S» (4,1,2,3,7) (state 0x3f800000 0x40000000 0x40400000 4)) =
    (0xCAFE000000000000,0x3F800000,0x40000000,0x40400000,0,false,(some 42),false,true,
 0xBBBB000000000000,true) := by
  simp only [«dfn'FNMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmsub_s_double_round_rte
example : observe («dfn'FNMSUB_S» (4,1,2,3,0) (state 0x3f800001 0x3f7ffffe 0x3f800000 0)) =
    (0xCAFE000080000000,0x3F800001,0x3F7FFFFE,0x3F800000,3,true,
 (some 0x80000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmsub_s_double_round_rtz
example : observe («dfn'FNMSUB_S» (4,1,2,3,1) (state 0x3f800001 0x3f7ffffe 0x3f800000 0)) =
    (0xCAFE000033800000,0x3F800001,0x3F7FFFFE,0x3F800000,3,true,
 (some 0x33800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmsub_s_double_round_down
example : observe («dfn'FNMSUB_S» (4,1,2,3,2) (state 0x3f800001 0x3f7ffffe 0x3f800000 0)) =
    (0xCAFE000033800000,0x3F800001,0x3F7FFFFE,0x3F800000,3,true,
 (some 0x33800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmsub_s_double_round_up
example : observe («dfn'FNMSUB_S» (4,1,2,3,3) (state 0x3f800001 0x3f7ffffe 0x3f800000 0)) =
    (0xCAFE000080000000,0x3F800001,0x3F7FFFFE,0x3F800000,3,true,
 (some 0x80000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmsub_s_double_round_dynamic_up
example : observe («dfn'FNMSUB_S» (4,1,2,3,7) (state 0x3f800001 0x3f7ffffe 0x3f800000 3)) =
    (0xCAFE000080000000,0x3F800001,0x3F7FFFFE,0x3F800000,3,true,
 (some 0x80000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmsub_s_double_round_invalid_static
example : observe («dfn'FNMSUB_S» (4,1,2,3,4) (state 0x3f800001 0x3f7ffffe 0x3f800000 0)) =
    (0xCAFE000000000000,0x3F800001,0x3F7FFFFE,0x3F800000,0,false,(some 42),false,true,
 0xBBBB000000000000,true) := by
  simp only [«dfn'FNMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmsub_s_double_round_invalid_dynamic
example : observe («dfn'FNMSUB_S» (4,1,2,3,7) (state 0x3f800001 0x3f7ffffe 0x3f800000 4)) =
    (0xCAFE000000000000,0x3F800001,0x3F7FFFFE,0x3F800000,0,false,(some 42),false,true,
 0xBBBB000000000000,true) := by
  simp only [«dfn'FNMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmsub_s_signed_zero_rte
example : observe («dfn'FNMSUB_S» (4,1,2,3,0) (state 0x80000000 0x40000000 0x0 0)) =
    (0xCAFE000000000000,0x80000000,0x40000000,0,3,true,(some 0),false,true,
 0xBBBB000000000000,false) := by
  simp only [«dfn'FNMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmsub_s_signed_zero_rtz
example : observe («dfn'FNMSUB_S» (4,1,2,3,1) (state 0x80000000 0x40000000 0x0 0)) =
    (0xCAFE000000000000,0x80000000,0x40000000,0,3,true,(some 0),false,true,
 0xBBBB000000000000,false) := by
  simp only [«dfn'FNMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmsub_s_signed_zero_down
example : observe («dfn'FNMSUB_S» (4,1,2,3,2) (state 0x80000000 0x40000000 0x0 0)) =
    (0xCAFE000000000000,0x80000000,0x40000000,0,3,true,(some 0),false,true,
 0xBBBB000000000000,false) := by
  simp only [«dfn'FNMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmsub_s_signed_zero_up
example : observe («dfn'FNMSUB_S» (4,1,2,3,3) (state 0x80000000 0x40000000 0x0 0)) =
    (0xCAFE000000000000,0x80000000,0x40000000,0,3,true,(some 0),false,true,
 0xBBBB000000000000,false) := by
  simp only [«dfn'FNMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmsub_s_infinity_rte
example : observe («dfn'FNMSUB_S» (4,1,2,3,0) (state 0x7f800000 0xbf800000 0x3f800000 0)) =
    (0xCAFE00007F800000,0x7F800000,0xBF800000,0x3F800000,3,true,
 (some 0x7F800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmsub_s_infinity_rtz
example : observe («dfn'FNMSUB_S» (4,1,2,3,1) (state 0x7f800000 0xbf800000 0x3f800000 0)) =
    (0xCAFE00007F800000,0x7F800000,0xBF800000,0x3F800000,3,true,
 (some 0x7F800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmsub_s_infinity_down
example : observe («dfn'FNMSUB_S» (4,1,2,3,2) (state 0x7f800000 0xbf800000 0x3f800000 0)) =
    (0xCAFE00007F800000,0x7F800000,0xBF800000,0x3F800000,3,true,
 (some 0x7F800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmsub_s_infinity_up
example : observe («dfn'FNMSUB_S» (4,1,2,3,3) (state 0x7f800000 0xbf800000 0x3f800000 0)) =
    (0xCAFE00007F800000,0x7F800000,0xBF800000,0x3F800000,3,true,
 (some 0x7F800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmsub_s_negative_finite_rte
example : observe («dfn'FNMSUB_S» (4,1,2,3,0) (state 0xbf800000 0x40000000 0x40400000 0)) =
    (0xCAFE000040A00000,0xBF800000,0x40000000,0x40400000,3,true,
 (some 0x40A00000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmsub_s_negative_finite_rtz
example : observe («dfn'FNMSUB_S» (4,1,2,3,1) (state 0xbf800000 0x40000000 0x40400000 0)) =
    (0xCAFE000040A00000,0xBF800000,0x40000000,0x40400000,3,true,
 (some 0x40A00000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmsub_s_negative_finite_down
example : observe («dfn'FNMSUB_S» (4,1,2,3,2) (state 0xbf800000 0x40000000 0x40400000 0)) =
    (0xCAFE000040A00000,0xBF800000,0x40000000,0x40400000,3,true,
 (some 0x40A00000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fnmsub_s_negative_finite_up
example : observe («dfn'FNMSUB_S» (4,1,2,3,3) (state 0xbf800000 0x40000000 0x40400000 0)) =
    (0xCAFE000040A00000,0xBF800000,0x40000000,0x40400000,3,true,
 (some 0x40A00000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMSUB_S», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel

-- Original fmadd_d_basic_rte
example : observe («dfn'FMADD_D» (4,1,2,3,0) (state 0x3ff0000000000000 0x4000000000000000 0x4008000000000000 0)) =
    (0x4014000000000000,0x3FF0000000000000,0x4000000000000000,
 0x4008000000000000,3,true,(some 0x4014000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmadd_d_basic_rtz
example : observe («dfn'FMADD_D» (4,1,2,3,1) (state 0x3ff0000000000000 0x4000000000000000 0x4008000000000000 0)) =
    (0x4014000000000000,0x3FF0000000000000,0x4000000000000000,
 0x4008000000000000,3,true,(some 0x4014000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmadd_d_basic_down
example : observe («dfn'FMADD_D» (4,1,2,3,2) (state 0x3ff0000000000000 0x4000000000000000 0x4008000000000000 0)) =
    (0x4014000000000000,0x3FF0000000000000,0x4000000000000000,
 0x4008000000000000,3,true,(some 0x4014000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmadd_d_basic_up
example : observe («dfn'FMADD_D» (4,1,2,3,3) (state 0x3ff0000000000000 0x4000000000000000 0x4008000000000000 0)) =
    (0x4014000000000000,0x3FF0000000000000,0x4000000000000000,
 0x4008000000000000,3,true,(some 0x4014000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmadd_d_basic_dynamic_up
example : observe («dfn'FMADD_D» (4,1,2,3,7) (state 0x3ff0000000000000 0x4000000000000000 0x4008000000000000 3)) =
    (0x4014000000000000,0x3FF0000000000000,0x4000000000000000,
 0x4008000000000000,3,true,(some 0x4014000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmadd_d_basic_invalid_static
example : observe («dfn'FMADD_D» (4,1,2,3,4) (state 0x3ff0000000000000 0x4000000000000000 0x4008000000000000 0)) =
    (0xCAFE000000000000,0x3FF0000000000000,0x4000000000000000,
 0x4008000000000000,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmadd_d_basic_invalid_dynamic
example : observe («dfn'FMADD_D» (4,1,2,3,7) (state 0x3ff0000000000000 0x4000000000000000 0x4008000000000000 4)) =
    (0xCAFE000000000000,0x3FF0000000000000,0x4000000000000000,
 0x4008000000000000,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmadd_d_double_round_rte
example : observe («dfn'FMADD_D» (4,1,2,3,0) (state 0x3ff0000000000001 0x3feffffffffffffe 0xbff0000000000000 0)) =
    (0,0x3FF0000000000001,0x3FEFFFFFFFFFFFFE,0xBFF0000000000000,3,true,(some 0),
 false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmadd_d_double_round_rtz
example : observe («dfn'FMADD_D» (4,1,2,3,1) (state 0x3ff0000000000001 0x3feffffffffffffe 0xbff0000000000000 0)) =
    (0xBCA0000000000000,0x3FF0000000000001,0x3FEFFFFFFFFFFFFE,
 0xBFF0000000000000,3,true,(some 0xBCA0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmadd_d_double_round_down
example : observe («dfn'FMADD_D» (4,1,2,3,2) (state 0x3ff0000000000001 0x3feffffffffffffe 0xbff0000000000000 0)) =
    (0xBCA0000000000000,0x3FF0000000000001,0x3FEFFFFFFFFFFFFE,
 0xBFF0000000000000,3,true,(some 0xBCA0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmadd_d_double_round_up
example : observe («dfn'FMADD_D» (4,1,2,3,3) (state 0x3ff0000000000001 0x3feffffffffffffe 0xbff0000000000000 0)) =
    (0,0x3FF0000000000001,0x3FEFFFFFFFFFFFFE,0xBFF0000000000000,3,true,(some 0),
 false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmadd_d_double_round_dynamic_up
example : observe («dfn'FMADD_D» (4,1,2,3,7) (state 0x3ff0000000000001 0x3feffffffffffffe 0xbff0000000000000 3)) =
    (0,0x3FF0000000000001,0x3FEFFFFFFFFFFFFE,0xBFF0000000000000,3,true,(some 0),
 false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmadd_d_double_round_invalid_static
example : observe («dfn'FMADD_D» (4,1,2,3,4) (state 0x3ff0000000000001 0x3feffffffffffffe 0xbff0000000000000 0)) =
    (0xCAFE000000000000,0x3FF0000000000001,0x3FEFFFFFFFFFFFFE,
 0xBFF0000000000000,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmadd_d_double_round_invalid_dynamic
example : observe («dfn'FMADD_D» (4,1,2,3,7) (state 0x3ff0000000000001 0x3feffffffffffffe 0xbff0000000000000 4)) =
    (0xCAFE000000000000,0x3FF0000000000001,0x3FEFFFFFFFFFFFFE,
 0xBFF0000000000000,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmadd_d_signed_zero_rte
example : observe («dfn'FMADD_D» (4,1,2,3,0) (state 0x8000000000000000 0x4000000000000000 0x0 0)) =
    (0,0x8000000000000000,0x4000000000000000,0,3,true,(some 0),false,true,
 0xBBBB000000000000,false) := by
  simp only [«dfn'FMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmadd_d_signed_zero_rtz
example : observe («dfn'FMADD_D» (4,1,2,3,1) (state 0x8000000000000000 0x4000000000000000 0x0 0)) =
    (0,0x8000000000000000,0x4000000000000000,0,3,true,(some 0),false,true,
 0xBBBB000000000000,false) := by
  simp only [«dfn'FMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmadd_d_signed_zero_down
example : observe («dfn'FMADD_D» (4,1,2,3,2) (state 0x8000000000000000 0x4000000000000000 0x0 0)) =
    (0x8000000000000000,0x8000000000000000,0x4000000000000000,0,3,true,
 (some 0x8000000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmadd_d_signed_zero_up
example : observe («dfn'FMADD_D» (4,1,2,3,3) (state 0x8000000000000000 0x4000000000000000 0x0 0)) =
    (0,0x8000000000000000,0x4000000000000000,0,3,true,(some 0),false,true,
 0xBBBB000000000000,false) := by
  simp only [«dfn'FMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmadd_d_infinity_rte
example : observe («dfn'FMADD_D» (4,1,2,3,0) (state 0x7ff0000000000000 0xbff0000000000000 0x3ff0000000000000 0)) =
    (0xFFF0000000000000,0x7FF0000000000000,0xBFF0000000000000,
 0x3FF0000000000000,3,true,(some 0xFFF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmadd_d_infinity_rtz
example : observe («dfn'FMADD_D» (4,1,2,3,1) (state 0x7ff0000000000000 0xbff0000000000000 0x3ff0000000000000 0)) =
    (0xFFF0000000000000,0x7FF0000000000000,0xBFF0000000000000,
 0x3FF0000000000000,3,true,(some 0xFFF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmadd_d_infinity_down
example : observe («dfn'FMADD_D» (4,1,2,3,2) (state 0x7ff0000000000000 0xbff0000000000000 0x3ff0000000000000 0)) =
    (0xFFF0000000000000,0x7FF0000000000000,0xBFF0000000000000,
 0x3FF0000000000000,3,true,(some 0xFFF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmadd_d_infinity_up
example : observe («dfn'FMADD_D» (4,1,2,3,3) (state 0x7ff0000000000000 0xbff0000000000000 0x3ff0000000000000 0)) =
    (0xFFF0000000000000,0x7FF0000000000000,0xBFF0000000000000,
 0x3FF0000000000000,3,true,(some 0xFFF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmadd_d_negative_finite_rte
example : observe («dfn'FMADD_D» (4,1,2,3,0) (state 0xbff0000000000000 0x4000000000000000 0x4008000000000000 0)) =
    (0x3FF0000000000000,0xBFF0000000000000,0x4000000000000000,
 0x4008000000000000,3,true,(some 0x3FF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmadd_d_negative_finite_rtz
example : observe («dfn'FMADD_D» (4,1,2,3,1) (state 0xbff0000000000000 0x4000000000000000 0x4008000000000000 0)) =
    (0x3FF0000000000000,0xBFF0000000000000,0x4000000000000000,
 0x4008000000000000,3,true,(some 0x3FF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmadd_d_negative_finite_down
example : observe («dfn'FMADD_D» (4,1,2,3,2) (state 0xbff0000000000000 0x4000000000000000 0x4008000000000000 0)) =
    (0x3FF0000000000000,0xBFF0000000000000,0x4000000000000000,
 0x4008000000000000,3,true,(some 0x3FF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmadd_d_negative_finite_up
example : observe («dfn'FMADD_D» (4,1,2,3,3) (state 0xbff0000000000000 0x4000000000000000 0x4008000000000000 0)) =
    (0x3FF0000000000000,0xBFF0000000000000,0x4000000000000000,
 0x4008000000000000,3,true,(some 0x3FF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmsub_d_basic_rte
example : observe («dfn'FMSUB_D» (4,1,2,3,0) (state 0x3ff0000000000000 0x4000000000000000 0x4008000000000000 0)) =
    (0xBFF0000000000000,0x3FF0000000000000,0x4000000000000000,
 0x4008000000000000,3,true,(some 0xBFF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmsub_d_basic_rtz
example : observe («dfn'FMSUB_D» (4,1,2,3,1) (state 0x3ff0000000000000 0x4000000000000000 0x4008000000000000 0)) =
    (0xBFF0000000000000,0x3FF0000000000000,0x4000000000000000,
 0x4008000000000000,3,true,(some 0xBFF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmsub_d_basic_down
example : observe («dfn'FMSUB_D» (4,1,2,3,2) (state 0x3ff0000000000000 0x4000000000000000 0x4008000000000000 0)) =
    (0xBFF0000000000000,0x3FF0000000000000,0x4000000000000000,
 0x4008000000000000,3,true,(some 0xBFF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmsub_d_basic_up
example : observe («dfn'FMSUB_D» (4,1,2,3,3) (state 0x3ff0000000000000 0x4000000000000000 0x4008000000000000 0)) =
    (0xBFF0000000000000,0x3FF0000000000000,0x4000000000000000,
 0x4008000000000000,3,true,(some 0xBFF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmsub_d_basic_dynamic_up
example : observe («dfn'FMSUB_D» (4,1,2,3,7) (state 0x3ff0000000000000 0x4000000000000000 0x4008000000000000 3)) =
    (0xBFF0000000000000,0x3FF0000000000000,0x4000000000000000,
 0x4008000000000000,3,true,(some 0xBFF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmsub_d_basic_invalid_static
example : observe («dfn'FMSUB_D» (4,1,2,3,4) (state 0x3ff0000000000000 0x4000000000000000 0x4008000000000000 0)) =
    (0xCAFE000000000000,0x3FF0000000000000,0x4000000000000000,
 0x4008000000000000,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmsub_d_basic_invalid_dynamic
example : observe («dfn'FMSUB_D» (4,1,2,3,7) (state 0x3ff0000000000000 0x4000000000000000 0x4008000000000000 4)) =
    (0xCAFE000000000000,0x3FF0000000000000,0x4000000000000000,
 0x4008000000000000,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmsub_d_double_round_rte
example : observe («dfn'FMSUB_D» (4,1,2,3,0) (state 0x3ff0000000000001 0x3feffffffffffffe 0x3ff0000000000000 0)) =
    (0,0x3FF0000000000001,0x3FEFFFFFFFFFFFFE,0x3FF0000000000000,3,true,(some 0),
 false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmsub_d_double_round_rtz
example : observe («dfn'FMSUB_D» (4,1,2,3,1) (state 0x3ff0000000000001 0x3feffffffffffffe 0x3ff0000000000000 0)) =
    (0xBCA0000000000000,0x3FF0000000000001,0x3FEFFFFFFFFFFFFE,
 0x3FF0000000000000,3,true,(some 0xBCA0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmsub_d_double_round_down
example : observe («dfn'FMSUB_D» (4,1,2,3,2) (state 0x3ff0000000000001 0x3feffffffffffffe 0x3ff0000000000000 0)) =
    (0xBCA0000000000000,0x3FF0000000000001,0x3FEFFFFFFFFFFFFE,
 0x3FF0000000000000,3,true,(some 0xBCA0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmsub_d_double_round_up
example : observe («dfn'FMSUB_D» (4,1,2,3,3) (state 0x3ff0000000000001 0x3feffffffffffffe 0x3ff0000000000000 0)) =
    (0,0x3FF0000000000001,0x3FEFFFFFFFFFFFFE,0x3FF0000000000000,3,true,(some 0),
 false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmsub_d_double_round_dynamic_up
example : observe («dfn'FMSUB_D» (4,1,2,3,7) (state 0x3ff0000000000001 0x3feffffffffffffe 0x3ff0000000000000 3)) =
    (0,0x3FF0000000000001,0x3FEFFFFFFFFFFFFE,0x3FF0000000000000,3,true,(some 0),
 false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmsub_d_double_round_invalid_static
example : observe («dfn'FMSUB_D» (4,1,2,3,4) (state 0x3ff0000000000001 0x3feffffffffffffe 0x3ff0000000000000 0)) =
    (0xCAFE000000000000,0x3FF0000000000001,0x3FEFFFFFFFFFFFFE,
 0x3FF0000000000000,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmsub_d_double_round_invalid_dynamic
example : observe («dfn'FMSUB_D» (4,1,2,3,7) (state 0x3ff0000000000001 0x3feffffffffffffe 0x3ff0000000000000 4)) =
    (0xCAFE000000000000,0x3FF0000000000001,0x3FEFFFFFFFFFFFFE,
 0x3FF0000000000000,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmsub_d_signed_zero_rte
example : observe («dfn'FMSUB_D» (4,1,2,3,0) (state 0x8000000000000000 0x4000000000000000 0x0 0)) =
    (0x8000000000000000,0x8000000000000000,0x4000000000000000,0,3,true,
 (some 0x8000000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmsub_d_signed_zero_rtz
example : observe («dfn'FMSUB_D» (4,1,2,3,1) (state 0x8000000000000000 0x4000000000000000 0x0 0)) =
    (0x8000000000000000,0x8000000000000000,0x4000000000000000,0,3,true,
 (some 0x8000000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmsub_d_signed_zero_down
example : observe («dfn'FMSUB_D» (4,1,2,3,2) (state 0x8000000000000000 0x4000000000000000 0x0 0)) =
    (0x8000000000000000,0x8000000000000000,0x4000000000000000,0,3,true,
 (some 0x8000000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmsub_d_signed_zero_up
example : observe («dfn'FMSUB_D» (4,1,2,3,3) (state 0x8000000000000000 0x4000000000000000 0x0 0)) =
    (0x8000000000000000,0x8000000000000000,0x4000000000000000,0,3,true,
 (some 0x8000000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmsub_d_infinity_rte
example : observe («dfn'FMSUB_D» (4,1,2,3,0) (state 0x7ff0000000000000 0xbff0000000000000 0x3ff0000000000000 0)) =
    (0xFFF0000000000000,0x7FF0000000000000,0xBFF0000000000000,
 0x3FF0000000000000,3,true,(some 0xFFF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmsub_d_infinity_rtz
example : observe («dfn'FMSUB_D» (4,1,2,3,1) (state 0x7ff0000000000000 0xbff0000000000000 0x3ff0000000000000 0)) =
    (0xFFF0000000000000,0x7FF0000000000000,0xBFF0000000000000,
 0x3FF0000000000000,3,true,(some 0xFFF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmsub_d_infinity_down
example : observe («dfn'FMSUB_D» (4,1,2,3,2) (state 0x7ff0000000000000 0xbff0000000000000 0x3ff0000000000000 0)) =
    (0xFFF0000000000000,0x7FF0000000000000,0xBFF0000000000000,
 0x3FF0000000000000,3,true,(some 0xFFF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmsub_d_infinity_up
example : observe («dfn'FMSUB_D» (4,1,2,3,3) (state 0x7ff0000000000000 0xbff0000000000000 0x3ff0000000000000 0)) =
    (0xFFF0000000000000,0x7FF0000000000000,0xBFF0000000000000,
 0x3FF0000000000000,3,true,(some 0xFFF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmsub_d_negative_finite_rte
example : observe («dfn'FMSUB_D» (4,1,2,3,0) (state 0xbff0000000000000 0x4000000000000000 0x4008000000000000 0)) =
    (0xC014000000000000,0xBFF0000000000000,0x4000000000000000,
 0x4008000000000000,3,true,(some 0xC014000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmsub_d_negative_finite_rtz
example : observe («dfn'FMSUB_D» (4,1,2,3,1) (state 0xbff0000000000000 0x4000000000000000 0x4008000000000000 0)) =
    (0xC014000000000000,0xBFF0000000000000,0x4000000000000000,
 0x4008000000000000,3,true,(some 0xC014000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmsub_d_negative_finite_down
example : observe («dfn'FMSUB_D» (4,1,2,3,2) (state 0xbff0000000000000 0x4000000000000000 0x4008000000000000 0)) =
    (0xC014000000000000,0xBFF0000000000000,0x4000000000000000,
 0x4008000000000000,3,true,(some 0xC014000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fmsub_d_negative_finite_up
example : observe («dfn'FMSUB_D» (4,1,2,3,3) (state 0xbff0000000000000 0x4000000000000000 0x4008000000000000 0)) =
    (0xC014000000000000,0xBFF0000000000000,0x4000000000000000,
 0x4008000000000000,3,true,(some 0xC014000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmadd_d_basic_rte
example : observe («dfn'FNMADD_D» (4,1,2,3,0) (state 0x3ff0000000000000 0x4000000000000000 0x4008000000000000 0)) =
    (0xC014000000000000,0x3FF0000000000000,0x4000000000000000,
 0x4008000000000000,3,true,(some 0xC014000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmadd_d_basic_rtz
example : observe («dfn'FNMADD_D» (4,1,2,3,1) (state 0x3ff0000000000000 0x4000000000000000 0x4008000000000000 0)) =
    (0xC014000000000000,0x3FF0000000000000,0x4000000000000000,
 0x4008000000000000,3,true,(some 0xC014000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmadd_d_basic_down
example : observe («dfn'FNMADD_D» (4,1,2,3,2) (state 0x3ff0000000000000 0x4000000000000000 0x4008000000000000 0)) =
    (0xC014000000000000,0x3FF0000000000000,0x4000000000000000,
 0x4008000000000000,3,true,(some 0xC014000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmadd_d_basic_up
example : observe («dfn'FNMADD_D» (4,1,2,3,3) (state 0x3ff0000000000000 0x4000000000000000 0x4008000000000000 0)) =
    (0xC014000000000000,0x3FF0000000000000,0x4000000000000000,
 0x4008000000000000,3,true,(some 0xC014000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmadd_d_basic_dynamic_up
example : observe («dfn'FNMADD_D» (4,1,2,3,7) (state 0x3ff0000000000000 0x4000000000000000 0x4008000000000000 3)) =
    (0xC014000000000000,0x3FF0000000000000,0x4000000000000000,
 0x4008000000000000,3,true,(some 0xC014000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmadd_d_basic_invalid_static
example : observe («dfn'FNMADD_D» (4,1,2,3,4) (state 0x3ff0000000000000 0x4000000000000000 0x4008000000000000 0)) =
    (0xCAFE000000000000,0x3FF0000000000000,0x4000000000000000,
 0x4008000000000000,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FNMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmadd_d_basic_invalid_dynamic
example : observe («dfn'FNMADD_D» (4,1,2,3,7) (state 0x3ff0000000000000 0x4000000000000000 0x4008000000000000 4)) =
    (0xCAFE000000000000,0x3FF0000000000000,0x4000000000000000,
 0x4008000000000000,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FNMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmadd_d_double_round_rte
example : observe («dfn'FNMADD_D» (4,1,2,3,0) (state 0x3ff0000000000001 0x3feffffffffffffe 0xbff0000000000000 0)) =
    (0x8000000000000000,0x3FF0000000000001,0x3FEFFFFFFFFFFFFE,
 0xBFF0000000000000,3,true,(some 0x8000000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmadd_d_double_round_rtz
example : observe («dfn'FNMADD_D» (4,1,2,3,1) (state 0x3ff0000000000001 0x3feffffffffffffe 0xbff0000000000000 0)) =
    (0x3CA0000000000000,0x3FF0000000000001,0x3FEFFFFFFFFFFFFE,
 0xBFF0000000000000,3,true,(some 0x3CA0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmadd_d_double_round_down
example : observe («dfn'FNMADD_D» (4,1,2,3,2) (state 0x3ff0000000000001 0x3feffffffffffffe 0xbff0000000000000 0)) =
    (0x3CA0000000000000,0x3FF0000000000001,0x3FEFFFFFFFFFFFFE,
 0xBFF0000000000000,3,true,(some 0x3CA0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmadd_d_double_round_up
example : observe («dfn'FNMADD_D» (4,1,2,3,3) (state 0x3ff0000000000001 0x3feffffffffffffe 0xbff0000000000000 0)) =
    (0x8000000000000000,0x3FF0000000000001,0x3FEFFFFFFFFFFFFE,
 0xBFF0000000000000,3,true,(some 0x8000000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmadd_d_double_round_dynamic_up
example : observe («dfn'FNMADD_D» (4,1,2,3,7) (state 0x3ff0000000000001 0x3feffffffffffffe 0xbff0000000000000 3)) =
    (0x8000000000000000,0x3FF0000000000001,0x3FEFFFFFFFFFFFFE,
 0xBFF0000000000000,3,true,(some 0x8000000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmadd_d_double_round_invalid_static
example : observe («dfn'FNMADD_D» (4,1,2,3,4) (state 0x3ff0000000000001 0x3feffffffffffffe 0xbff0000000000000 0)) =
    (0xCAFE000000000000,0x3FF0000000000001,0x3FEFFFFFFFFFFFFE,
 0xBFF0000000000000,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FNMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmadd_d_double_round_invalid_dynamic
example : observe («dfn'FNMADD_D» (4,1,2,3,7) (state 0x3ff0000000000001 0x3feffffffffffffe 0xbff0000000000000 4)) =
    (0xCAFE000000000000,0x3FF0000000000001,0x3FEFFFFFFFFFFFFE,
 0xBFF0000000000000,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FNMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmadd_d_signed_zero_rte
example : observe («dfn'FNMADD_D» (4,1,2,3,0) (state 0x8000000000000000 0x4000000000000000 0x0 0)) =
    (0x8000000000000000,0x8000000000000000,0x4000000000000000,0,3,true,
 (some 0x8000000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmadd_d_signed_zero_rtz
example : observe («dfn'FNMADD_D» (4,1,2,3,1) (state 0x8000000000000000 0x4000000000000000 0x0 0)) =
    (0x8000000000000000,0x8000000000000000,0x4000000000000000,0,3,true,
 (some 0x8000000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmadd_d_signed_zero_down
example : observe («dfn'FNMADD_D» (4,1,2,3,2) (state 0x8000000000000000 0x4000000000000000 0x0 0)) =
    (0,0x8000000000000000,0x4000000000000000,0,3,true,(some 0),false,true,
 0xBBBB000000000000,false) := by
  simp only [«dfn'FNMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmadd_d_signed_zero_up
example : observe («dfn'FNMADD_D» (4,1,2,3,3) (state 0x8000000000000000 0x4000000000000000 0x0 0)) =
    (0x8000000000000000,0x8000000000000000,0x4000000000000000,0,3,true,
 (some 0x8000000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmadd_d_infinity_rte
example : observe («dfn'FNMADD_D» (4,1,2,3,0) (state 0x7ff0000000000000 0xbff0000000000000 0x3ff0000000000000 0)) =
    (0x7FF0000000000000,0x7FF0000000000000,0xBFF0000000000000,
 0x3FF0000000000000,3,true,(some 0x7FF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmadd_d_infinity_rtz
example : observe («dfn'FNMADD_D» (4,1,2,3,1) (state 0x7ff0000000000000 0xbff0000000000000 0x3ff0000000000000 0)) =
    (0x7FF0000000000000,0x7FF0000000000000,0xBFF0000000000000,
 0x3FF0000000000000,3,true,(some 0x7FF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmadd_d_infinity_down
example : observe («dfn'FNMADD_D» (4,1,2,3,2) (state 0x7ff0000000000000 0xbff0000000000000 0x3ff0000000000000 0)) =
    (0x7FF0000000000000,0x7FF0000000000000,0xBFF0000000000000,
 0x3FF0000000000000,3,true,(some 0x7FF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmadd_d_infinity_up
example : observe («dfn'FNMADD_D» (4,1,2,3,3) (state 0x7ff0000000000000 0xbff0000000000000 0x3ff0000000000000 0)) =
    (0x7FF0000000000000,0x7FF0000000000000,0xBFF0000000000000,
 0x3FF0000000000000,3,true,(some 0x7FF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmadd_d_negative_finite_rte
example : observe («dfn'FNMADD_D» (4,1,2,3,0) (state 0xbff0000000000000 0x4000000000000000 0x4008000000000000 0)) =
    (0xBFF0000000000000,0xBFF0000000000000,0x4000000000000000,
 0x4008000000000000,3,true,(some 0xBFF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmadd_d_negative_finite_rtz
example : observe («dfn'FNMADD_D» (4,1,2,3,1) (state 0xbff0000000000000 0x4000000000000000 0x4008000000000000 0)) =
    (0xBFF0000000000000,0xBFF0000000000000,0x4000000000000000,
 0x4008000000000000,3,true,(some 0xBFF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmadd_d_negative_finite_down
example : observe («dfn'FNMADD_D» (4,1,2,3,2) (state 0xbff0000000000000 0x4000000000000000 0x4008000000000000 0)) =
    (0xBFF0000000000000,0xBFF0000000000000,0x4000000000000000,
 0x4008000000000000,3,true,(some 0xBFF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmadd_d_negative_finite_up
example : observe («dfn'FNMADD_D» (4,1,2,3,3) (state 0xbff0000000000000 0x4000000000000000 0x4008000000000000 0)) =
    (0xBFF0000000000000,0xBFF0000000000000,0x4000000000000000,
 0x4008000000000000,3,true,(some 0xBFF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMADD_D», holFloatMul, holFloatAdd,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmsub_d_basic_rte
example : observe («dfn'FNMSUB_D» (4,1,2,3,0) (state 0x3ff0000000000000 0x4000000000000000 0x4008000000000000 0)) =
    (0x3FF0000000000000,0x3FF0000000000000,0x4000000000000000,
 0x4008000000000000,3,true,(some 0x3FF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmsub_d_basic_rtz
example : observe («dfn'FNMSUB_D» (4,1,2,3,1) (state 0x3ff0000000000000 0x4000000000000000 0x4008000000000000 0)) =
    (0x3FF0000000000000,0x3FF0000000000000,0x4000000000000000,
 0x4008000000000000,3,true,(some 0x3FF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmsub_d_basic_down
example : observe («dfn'FNMSUB_D» (4,1,2,3,2) (state 0x3ff0000000000000 0x4000000000000000 0x4008000000000000 0)) =
    (0x3FF0000000000000,0x3FF0000000000000,0x4000000000000000,
 0x4008000000000000,3,true,(some 0x3FF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmsub_d_basic_up
example : observe («dfn'FNMSUB_D» (4,1,2,3,3) (state 0x3ff0000000000000 0x4000000000000000 0x4008000000000000 0)) =
    (0x3FF0000000000000,0x3FF0000000000000,0x4000000000000000,
 0x4008000000000000,3,true,(some 0x3FF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmsub_d_basic_dynamic_up
example : observe («dfn'FNMSUB_D» (4,1,2,3,7) (state 0x3ff0000000000000 0x4000000000000000 0x4008000000000000 3)) =
    (0x3FF0000000000000,0x3FF0000000000000,0x4000000000000000,
 0x4008000000000000,3,true,(some 0x3FF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmsub_d_basic_invalid_static
example : observe («dfn'FNMSUB_D» (4,1,2,3,4) (state 0x3ff0000000000000 0x4000000000000000 0x4008000000000000 0)) =
    (0xCAFE000000000000,0x3FF0000000000000,0x4000000000000000,
 0x4008000000000000,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FNMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmsub_d_basic_invalid_dynamic
example : observe («dfn'FNMSUB_D» (4,1,2,3,7) (state 0x3ff0000000000000 0x4000000000000000 0x4008000000000000 4)) =
    (0xCAFE000000000000,0x3FF0000000000000,0x4000000000000000,
 0x4008000000000000,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FNMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmsub_d_double_round_rte
example : observe («dfn'FNMSUB_D» (4,1,2,3,0) (state 0x3ff0000000000001 0x3feffffffffffffe 0x3ff0000000000000 0)) =
    (0x8000000000000000,0x3FF0000000000001,0x3FEFFFFFFFFFFFFE,
 0x3FF0000000000000,3,true,(some 0x8000000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmsub_d_double_round_rtz
example : observe («dfn'FNMSUB_D» (4,1,2,3,1) (state 0x3ff0000000000001 0x3feffffffffffffe 0x3ff0000000000000 0)) =
    (0x3CA0000000000000,0x3FF0000000000001,0x3FEFFFFFFFFFFFFE,
 0x3FF0000000000000,3,true,(some 0x3CA0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmsub_d_double_round_down
example : observe («dfn'FNMSUB_D» (4,1,2,3,2) (state 0x3ff0000000000001 0x3feffffffffffffe 0x3ff0000000000000 0)) =
    (0x3CA0000000000000,0x3FF0000000000001,0x3FEFFFFFFFFFFFFE,
 0x3FF0000000000000,3,true,(some 0x3CA0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmsub_d_double_round_up
example : observe («dfn'FNMSUB_D» (4,1,2,3,3) (state 0x3ff0000000000001 0x3feffffffffffffe 0x3ff0000000000000 0)) =
    (0x8000000000000000,0x3FF0000000000001,0x3FEFFFFFFFFFFFFE,
 0x3FF0000000000000,3,true,(some 0x8000000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmsub_d_double_round_dynamic_up
example : observe («dfn'FNMSUB_D» (4,1,2,3,7) (state 0x3ff0000000000001 0x3feffffffffffffe 0x3ff0000000000000 3)) =
    (0x8000000000000000,0x3FF0000000000001,0x3FEFFFFFFFFFFFFE,
 0x3FF0000000000000,3,true,(some 0x8000000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmsub_d_double_round_invalid_static
example : observe («dfn'FNMSUB_D» (4,1,2,3,4) (state 0x3ff0000000000001 0x3feffffffffffffe 0x3ff0000000000000 0)) =
    (0xCAFE000000000000,0x3FF0000000000001,0x3FEFFFFFFFFFFFFE,
 0x3FF0000000000000,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FNMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmsub_d_double_round_invalid_dynamic
example : observe («dfn'FNMSUB_D» (4,1,2,3,7) (state 0x3ff0000000000001 0x3feffffffffffffe 0x3ff0000000000000 4)) =
    (0xCAFE000000000000,0x3FF0000000000001,0x3FEFFFFFFFFFFFFE,
 0x3FF0000000000000,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FNMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmsub_d_signed_zero_rte
example : observe («dfn'FNMSUB_D» (4,1,2,3,0) (state 0x8000000000000000 0x4000000000000000 0x0 0)) =
    (0,0x8000000000000000,0x4000000000000000,0,3,true,(some 0),false,true,
 0xBBBB000000000000,false) := by
  simp only [«dfn'FNMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmsub_d_signed_zero_rtz
example : observe («dfn'FNMSUB_D» (4,1,2,3,1) (state 0x8000000000000000 0x4000000000000000 0x0 0)) =
    (0,0x8000000000000000,0x4000000000000000,0,3,true,(some 0),false,true,
 0xBBBB000000000000,false) := by
  simp only [«dfn'FNMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmsub_d_signed_zero_down
example : observe («dfn'FNMSUB_D» (4,1,2,3,2) (state 0x8000000000000000 0x4000000000000000 0x0 0)) =
    (0,0x8000000000000000,0x4000000000000000,0,3,true,(some 0),false,true,
 0xBBBB000000000000,false) := by
  simp only [«dfn'FNMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmsub_d_signed_zero_up
example : observe («dfn'FNMSUB_D» (4,1,2,3,3) (state 0x8000000000000000 0x4000000000000000 0x0 0)) =
    (0,0x8000000000000000,0x4000000000000000,0,3,true,(some 0),false,true,
 0xBBBB000000000000,false) := by
  simp only [«dfn'FNMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmsub_d_infinity_rte
example : observe («dfn'FNMSUB_D» (4,1,2,3,0) (state 0x7ff0000000000000 0xbff0000000000000 0x3ff0000000000000 0)) =
    (0x7FF0000000000000,0x7FF0000000000000,0xBFF0000000000000,
 0x3FF0000000000000,3,true,(some 0x7FF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmsub_d_infinity_rtz
example : observe («dfn'FNMSUB_D» (4,1,2,3,1) (state 0x7ff0000000000000 0xbff0000000000000 0x3ff0000000000000 0)) =
    (0x7FF0000000000000,0x7FF0000000000000,0xBFF0000000000000,
 0x3FF0000000000000,3,true,(some 0x7FF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmsub_d_infinity_down
example : observe («dfn'FNMSUB_D» (4,1,2,3,2) (state 0x7ff0000000000000 0xbff0000000000000 0x3ff0000000000000 0)) =
    (0x7FF0000000000000,0x7FF0000000000000,0xBFF0000000000000,
 0x3FF0000000000000,3,true,(some 0x7FF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmsub_d_infinity_up
example : observe («dfn'FNMSUB_D» (4,1,2,3,3) (state 0x7ff0000000000000 0xbff0000000000000 0x3ff0000000000000 0)) =
    (0x7FF0000000000000,0x7FF0000000000000,0xBFF0000000000000,
 0x3FF0000000000000,3,true,(some 0x7FF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmsub_d_negative_finite_rte
example : observe («dfn'FNMSUB_D» (4,1,2,3,0) (state 0xbff0000000000000 0x4000000000000000 0x4008000000000000 0)) =
    (0x4014000000000000,0xBFF0000000000000,0x4000000000000000,
 0x4008000000000000,3,true,(some 0x4014000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmsub_d_negative_finite_rtz
example : observe («dfn'FNMSUB_D» (4,1,2,3,1) (state 0xbff0000000000000 0x4000000000000000 0x4008000000000000 0)) =
    (0x4014000000000000,0xBFF0000000000000,0x4000000000000000,
 0x4008000000000000,3,true,(some 0x4014000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmsub_d_negative_finite_down
example : observe («dfn'FNMSUB_D» (4,1,2,3,2) (state 0xbff0000000000000 0x4000000000000000 0x4008000000000000 0)) =
    (0x4014000000000000,0xBFF0000000000000,0x4000000000000000,
 0x4008000000000000,3,true,(some 0x4014000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

-- Original fnmsub_d_negative_finite_up
example : observe («dfn'FNMSUB_D» (4,1,2,3,3) (state 0xbff0000000000000 0x4000000000000000 0x4008000000000000 0)) =
    (0x4014000000000000,0xBFF0000000000000,0x4000000000000000,
 0x4008000000000000,3,true,(some 0x4014000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FNMSUB_D», holFloatMul, holFloatSub,
    holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel

end Flapjack.Test.L3RiscvMaddParity
