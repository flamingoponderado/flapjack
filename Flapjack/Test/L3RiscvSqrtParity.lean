import Flapjack.RiscV.L3.Defs
/-! Complete original square-root state equations; finite rounding and NaN
choices remain symbolic. Numerical special/trap fixtures are appended from the
fresh original capture. Rational cuts retain docs/SOUNDNESS.md item 8. -/
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 2048
namespace Flapjack.Test.L3RiscvSqrtParity
open Flapjack.RiscV.L3 Flapjack
private def state (a b : BitVec 64) (frm : BitVec 3) : riscv_state :=
  { (default : riscv_state) with
    procID := 7
    c_gpr := fun _ _ => 99
    c_fpr := fun c r => if c = 7 then if r = 1 then a else if r = 2 then b
      else 0xcafe000000000000 else 0xbbbb000000000000
    c_NextFetch := fun _ => none
    c_update := fun _ => { (default : StateDelta) with data1 := some 42 }
    c_UCSR := fun _ => { (default : UserCSR) with
      fpcsr := { (default : FPCSR) with NV := false, NX := true, FRM := frm } }
    c_MCSR := fun _ => { (default : MachineCSR) with
      mstatus := { (default : mstatus) with MFS := 0, MSD := false } } }
private def observe (s : riscv_state) :=
  (FPRD 3 s, FPRD 1 s, FPRD 2 s, (MCSR s).mstatus.MFS, (MCSR s).mstatus.MSD,
    (Delta s).data1, (fcsr s).NV, (fcsr s).NX, s.c_fpr 8 3,
    match NextFetch s with
    | some (.Trap t) => decide (t.trap = ExceptionType.Illegal_Instr ∧ t.badaddr = none)
    | _ => false)


-- Original fsqrt_s_four_rte
example : «dfn'FSQRT_S» (3,1,0) (state 0x40800000 0x42 0) =
    writeFPRS (3,holFloatToFp32 ((holFloatRoundWithFlagsSqrt .roundTiesToEven false (holFloatToReal (holFp32ToFloat 0x40800000))).2)) (state 0x40800000 0x42 0) := by
  change writeFPRS (3,holFloatToFp32
    (holFloatSqrt .roundTiesToEven (holFp32ToFloat 0x40800000)).2) (state 0x40800000 0x42 0) = _
  have hs : (holFp32ToFloat 0x40800000).sign = 0 := by decide +kernel
  have hv : holFloatValue (holFp32ToFloat 0x40800000) = .float (holFloatToReal (holFp32ToFloat 0x40800000)) := by decide +kernel
  simp only [holFloatSqrt, if_pos hs, hv]

-- Original fsqrt_s_four_rtz
example : «dfn'FSQRT_S» (3,1,1) (state 0x40800000 0x42 0) =
    writeFPRS (3,holFloatToFp32 ((holFloatRoundWithFlagsSqrt .roundTowardZero false (holFloatToReal (holFp32ToFloat 0x40800000))).2)) (state 0x40800000 0x42 0) := by
  change writeFPRS (3,holFloatToFp32
    (holFloatSqrt .roundTowardZero (holFp32ToFloat 0x40800000)).2) (state 0x40800000 0x42 0) = _
  have hs : (holFp32ToFloat 0x40800000).sign = 0 := by decide +kernel
  have hv : holFloatValue (holFp32ToFloat 0x40800000) = .float (holFloatToReal (holFp32ToFloat 0x40800000)) := by decide +kernel
  simp only [holFloatSqrt, if_pos hs, hv]

-- Original fsqrt_s_four_down
example : «dfn'FSQRT_S» (3,1,2) (state 0x40800000 0x42 0) =
    writeFPRS (3,holFloatToFp32 ((holFloatRoundWithFlagsSqrt .roundTowardNegative false (holFloatToReal (holFp32ToFloat 0x40800000))).2)) (state 0x40800000 0x42 0) := by
  change writeFPRS (3,holFloatToFp32
    (holFloatSqrt .roundTowardNegative (holFp32ToFloat 0x40800000)).2) (state 0x40800000 0x42 0) = _
  have hs : (holFp32ToFloat 0x40800000).sign = 0 := by decide +kernel
  have hv : holFloatValue (holFp32ToFloat 0x40800000) = .float (holFloatToReal (holFp32ToFloat 0x40800000)) := by decide +kernel
  simp only [holFloatSqrt, if_pos hs, hv]

-- Original fsqrt_s_four_up
example : «dfn'FSQRT_S» (3,1,3) (state 0x40800000 0x42 0) =
    writeFPRS (3,holFloatToFp32 ((holFloatRoundWithFlagsSqrt .roundTowardPositive false (holFloatToReal (holFp32ToFloat 0x40800000))).2)) (state 0x40800000 0x42 0) := by
  change writeFPRS (3,holFloatToFp32
    (holFloatSqrt .roundTowardPositive (holFp32ToFloat 0x40800000)).2) (state 0x40800000 0x42 0) = _
  have hs : (holFp32ToFloat 0x40800000).sign = 0 := by decide +kernel
  have hv : holFloatValue (holFp32ToFloat 0x40800000) = .float (holFloatToReal (holFp32ToFloat 0x40800000)) := by decide +kernel
  simp only [holFloatSqrt, if_pos hs, hv]

-- Original fsqrt_s_four_dynamic_up
example : «dfn'FSQRT_S» (3,1,7) (state 0x40800000 0x42 3) =
    writeFPRS (3,holFloatToFp32 ((holFloatRoundWithFlagsSqrt .roundTowardPositive false (holFloatToReal (holFp32ToFloat 0x40800000))).2)) (state 0x40800000 0x42 3) := by
  change writeFPRS (3,holFloatToFp32
    (holFloatSqrt .roundTowardPositive (holFp32ToFloat 0x40800000)).2) (state 0x40800000 0x42 3) = _
  have hs : (holFp32ToFloat 0x40800000).sign = 0 := by decide +kernel
  have hv : holFloatValue (holFp32ToFloat 0x40800000) = .float (holFloatToReal (holFp32ToFloat 0x40800000)) := by decide +kernel
  simp only [holFloatSqrt, if_pos hs, hv]

-- Original fsqrt_s_negative_one_rte
example : «dfn'FSQRT_S» (3,1,0) (state 0xbf800000 0x42 0) =
    writeFPRS (3,holFloatToFp32 (holFloatSomeQnan (.fpSqrt .roundTiesToEven (holFp32ToFloat 0xbf800000)))) (state 0xbf800000 0x42 0) := by
  change writeFPRS (3,holFloatToFp32
    (holFloatSqrt .roundTiesToEven (holFp32ToFloat 0xbf800000)).2) (state 0xbf800000 0x42 0) = _
  have hs : (holFp32ToFloat 0xbf800000).sign ≠ 0 := by decide +kernel
  have hz : (holFp32ToFloat 0xbf800000) ≠ holFloatMinusZero _ _ := by decide +kernel
  simp only [holFloatSqrt, if_neg hs, if_neg hz]

-- Original fsqrt_s_negative_one_rtz
example : «dfn'FSQRT_S» (3,1,1) (state 0xbf800000 0x42 0) =
    writeFPRS (3,holFloatToFp32 (holFloatSomeQnan (.fpSqrt .roundTowardZero (holFp32ToFloat 0xbf800000)))) (state 0xbf800000 0x42 0) := by
  change writeFPRS (3,holFloatToFp32
    (holFloatSqrt .roundTowardZero (holFp32ToFloat 0xbf800000)).2) (state 0xbf800000 0x42 0) = _
  have hs : (holFp32ToFloat 0xbf800000).sign ≠ 0 := by decide +kernel
  have hz : (holFp32ToFloat 0xbf800000) ≠ holFloatMinusZero _ _ := by decide +kernel
  simp only [holFloatSqrt, if_neg hs, if_neg hz]

-- Original fsqrt_s_negative_one_down
example : «dfn'FSQRT_S» (3,1,2) (state 0xbf800000 0x42 0) =
    writeFPRS (3,holFloatToFp32 (holFloatSomeQnan (.fpSqrt .roundTowardNegative (holFp32ToFloat 0xbf800000)))) (state 0xbf800000 0x42 0) := by
  change writeFPRS (3,holFloatToFp32
    (holFloatSqrt .roundTowardNegative (holFp32ToFloat 0xbf800000)).2) (state 0xbf800000 0x42 0) = _
  have hs : (holFp32ToFloat 0xbf800000).sign ≠ 0 := by decide +kernel
  have hz : (holFp32ToFloat 0xbf800000) ≠ holFloatMinusZero _ _ := by decide +kernel
  simp only [holFloatSqrt, if_neg hs, if_neg hz]

-- Original fsqrt_s_negative_one_up
example : «dfn'FSQRT_S» (3,1,3) (state 0xbf800000 0x42 0) =
    writeFPRS (3,holFloatToFp32 (holFloatSomeQnan (.fpSqrt .roundTowardPositive (holFp32ToFloat 0xbf800000)))) (state 0xbf800000 0x42 0) := by
  change writeFPRS (3,holFloatToFp32
    (holFloatSqrt .roundTowardPositive (holFp32ToFloat 0xbf800000)).2) (state 0xbf800000 0x42 0) = _
  have hs : (holFp32ToFloat 0xbf800000).sign ≠ 0 := by decide +kernel
  have hz : (holFp32ToFloat 0xbf800000) ≠ holFloatMinusZero _ _ := by decide +kernel
  simp only [holFloatSqrt, if_neg hs, if_neg hz]

-- Original fsqrt_s_negative_one_dynamic_up
example : «dfn'FSQRT_S» (3,1,7) (state 0xbf800000 0x42 3) =
    writeFPRS (3,holFloatToFp32 (holFloatSomeQnan (.fpSqrt .roundTowardPositive (holFp32ToFloat 0xbf800000)))) (state 0xbf800000 0x42 3) := by
  change writeFPRS (3,holFloatToFp32
    (holFloatSqrt .roundTowardPositive (holFp32ToFloat 0xbf800000)).2) (state 0xbf800000 0x42 3) = _
  have hs : (holFp32ToFloat 0xbf800000).sign ≠ 0 := by decide +kernel
  have hz : (holFp32ToFloat 0xbf800000) ≠ holFloatMinusZero _ _ := by decide +kernel
  simp only [holFloatSqrt, if_neg hs, if_neg hz]

-- Original fsqrt_d_four_rte
example : «dfn'FSQRT_D» (3,1,0) (state 0x4010000000000000 0x42 0) =
    writeFPRD (3,holFloatToFp64 ((holFloatRoundWithFlagsSqrt .roundTiesToEven false (holFloatToReal (holFp64ToFloat 0x4010000000000000))).2)) (state 0x4010000000000000 0x42 0) := by
  change writeFPRD (3,holFloatToFp64
    (holFloatSqrt .roundTiesToEven (holFp64ToFloat 0x4010000000000000)).2) (state 0x4010000000000000 0x42 0) = _
  have hs : (holFp64ToFloat 0x4010000000000000).sign = 0 := by decide +kernel
  have hv : holFloatValue (holFp64ToFloat 0x4010000000000000) = .float (holFloatToReal (holFp64ToFloat 0x4010000000000000)) := by decide +kernel
  simp only [holFloatSqrt, if_pos hs, hv]

-- Original fsqrt_d_four_rtz
example : «dfn'FSQRT_D» (3,1,1) (state 0x4010000000000000 0x42 0) =
    writeFPRD (3,holFloatToFp64 ((holFloatRoundWithFlagsSqrt .roundTowardZero false (holFloatToReal (holFp64ToFloat 0x4010000000000000))).2)) (state 0x4010000000000000 0x42 0) := by
  change writeFPRD (3,holFloatToFp64
    (holFloatSqrt .roundTowardZero (holFp64ToFloat 0x4010000000000000)).2) (state 0x4010000000000000 0x42 0) = _
  have hs : (holFp64ToFloat 0x4010000000000000).sign = 0 := by decide +kernel
  have hv : holFloatValue (holFp64ToFloat 0x4010000000000000) = .float (holFloatToReal (holFp64ToFloat 0x4010000000000000)) := by decide +kernel
  simp only [holFloatSqrt, if_pos hs, hv]

-- Original fsqrt_d_four_down
example : «dfn'FSQRT_D» (3,1,2) (state 0x4010000000000000 0x42 0) =
    writeFPRD (3,holFloatToFp64 ((holFloatRoundWithFlagsSqrt .roundTowardNegative false (holFloatToReal (holFp64ToFloat 0x4010000000000000))).2)) (state 0x4010000000000000 0x42 0) := by
  change writeFPRD (3,holFloatToFp64
    (holFloatSqrt .roundTowardNegative (holFp64ToFloat 0x4010000000000000)).2) (state 0x4010000000000000 0x42 0) = _
  have hs : (holFp64ToFloat 0x4010000000000000).sign = 0 := by decide +kernel
  have hv : holFloatValue (holFp64ToFloat 0x4010000000000000) = .float (holFloatToReal (holFp64ToFloat 0x4010000000000000)) := by decide +kernel
  simp only [holFloatSqrt, if_pos hs, hv]

-- Original fsqrt_d_four_up
example : «dfn'FSQRT_D» (3,1,3) (state 0x4010000000000000 0x42 0) =
    writeFPRD (3,holFloatToFp64 ((holFloatRoundWithFlagsSqrt .roundTowardPositive false (holFloatToReal (holFp64ToFloat 0x4010000000000000))).2)) (state 0x4010000000000000 0x42 0) := by
  change writeFPRD (3,holFloatToFp64
    (holFloatSqrt .roundTowardPositive (holFp64ToFloat 0x4010000000000000)).2) (state 0x4010000000000000 0x42 0) = _
  have hs : (holFp64ToFloat 0x4010000000000000).sign = 0 := by decide +kernel
  have hv : holFloatValue (holFp64ToFloat 0x4010000000000000) = .float (holFloatToReal (holFp64ToFloat 0x4010000000000000)) := by decide +kernel
  simp only [holFloatSqrt, if_pos hs, hv]

-- Original fsqrt_d_four_dynamic_up
example : «dfn'FSQRT_D» (3,1,7) (state 0x4010000000000000 0x42 3) =
    writeFPRD (3,holFloatToFp64 ((holFloatRoundWithFlagsSqrt .roundTowardPositive false (holFloatToReal (holFp64ToFloat 0x4010000000000000))).2)) (state 0x4010000000000000 0x42 3) := by
  change writeFPRD (3,holFloatToFp64
    (holFloatSqrt .roundTowardPositive (holFp64ToFloat 0x4010000000000000)).2) (state 0x4010000000000000 0x42 3) = _
  have hs : (holFp64ToFloat 0x4010000000000000).sign = 0 := by decide +kernel
  have hv : holFloatValue (holFp64ToFloat 0x4010000000000000) = .float (holFloatToReal (holFp64ToFloat 0x4010000000000000)) := by decide +kernel
  simp only [holFloatSqrt, if_pos hs, hv]

-- Original fsqrt_d_negative_one_rte
example : «dfn'FSQRT_D» (3,1,0) (state 0xbff0000000000000 0x42 0) =
    writeFPRD (3,holFloatToFp64 (holFloatSomeQnan (.fpSqrt .roundTiesToEven (holFp64ToFloat 0xbff0000000000000)))) (state 0xbff0000000000000 0x42 0) := by
  change writeFPRD (3,holFloatToFp64
    (holFloatSqrt .roundTiesToEven (holFp64ToFloat 0xbff0000000000000)).2) (state 0xbff0000000000000 0x42 0) = _
  have hs : (holFp64ToFloat 0xbff0000000000000).sign ≠ 0 := by decide +kernel
  have hz : (holFp64ToFloat 0xbff0000000000000) ≠ holFloatMinusZero _ _ := by decide +kernel
  simp only [holFloatSqrt, if_neg hs, if_neg hz]

-- Original fsqrt_d_negative_one_rtz
example : «dfn'FSQRT_D» (3,1,1) (state 0xbff0000000000000 0x42 0) =
    writeFPRD (3,holFloatToFp64 (holFloatSomeQnan (.fpSqrt .roundTowardZero (holFp64ToFloat 0xbff0000000000000)))) (state 0xbff0000000000000 0x42 0) := by
  change writeFPRD (3,holFloatToFp64
    (holFloatSqrt .roundTowardZero (holFp64ToFloat 0xbff0000000000000)).2) (state 0xbff0000000000000 0x42 0) = _
  have hs : (holFp64ToFloat 0xbff0000000000000).sign ≠ 0 := by decide +kernel
  have hz : (holFp64ToFloat 0xbff0000000000000) ≠ holFloatMinusZero _ _ := by decide +kernel
  simp only [holFloatSqrt, if_neg hs, if_neg hz]

-- Original fsqrt_d_negative_one_down
example : «dfn'FSQRT_D» (3,1,2) (state 0xbff0000000000000 0x42 0) =
    writeFPRD (3,holFloatToFp64 (holFloatSomeQnan (.fpSqrt .roundTowardNegative (holFp64ToFloat 0xbff0000000000000)))) (state 0xbff0000000000000 0x42 0) := by
  change writeFPRD (3,holFloatToFp64
    (holFloatSqrt .roundTowardNegative (holFp64ToFloat 0xbff0000000000000)).2) (state 0xbff0000000000000 0x42 0) = _
  have hs : (holFp64ToFloat 0xbff0000000000000).sign ≠ 0 := by decide +kernel
  have hz : (holFp64ToFloat 0xbff0000000000000) ≠ holFloatMinusZero _ _ := by decide +kernel
  simp only [holFloatSqrt, if_neg hs, if_neg hz]

-- Original fsqrt_d_negative_one_up
example : «dfn'FSQRT_D» (3,1,3) (state 0xbff0000000000000 0x42 0) =
    writeFPRD (3,holFloatToFp64 (holFloatSomeQnan (.fpSqrt .roundTowardPositive (holFp64ToFloat 0xbff0000000000000)))) (state 0xbff0000000000000 0x42 0) := by
  change writeFPRD (3,holFloatToFp64
    (holFloatSqrt .roundTowardPositive (holFp64ToFloat 0xbff0000000000000)).2) (state 0xbff0000000000000 0x42 0) = _
  have hs : (holFp64ToFloat 0xbff0000000000000).sign ≠ 0 := by decide +kernel
  have hz : (holFp64ToFloat 0xbff0000000000000) ≠ holFloatMinusZero _ _ := by decide +kernel
  simp only [holFloatSqrt, if_neg hs, if_neg hz]

-- Original fsqrt_d_negative_one_dynamic_up
example : «dfn'FSQRT_D» (3,1,7) (state 0xbff0000000000000 0x42 3) =
    writeFPRD (3,holFloatToFp64 (holFloatSomeQnan (.fpSqrt .roundTowardPositive (holFp64ToFloat 0xbff0000000000000)))) (state 0xbff0000000000000 0x42 3) := by
  change writeFPRD (3,holFloatToFp64
    (holFloatSqrt .roundTowardPositive (holFp64ToFloat 0xbff0000000000000)).2) (state 0xbff0000000000000 0x42 3) = _
  have hs : (holFp64ToFloat 0xbff0000000000000).sign ≠ 0 := by decide +kernel
  have hz : (holFp64ToFloat 0xbff0000000000000) ≠ holFloatMinusZero _ _ := by decide +kernel
  simp only [holFloatSqrt, if_neg hs, if_neg hz]


-- Original fsqrt_s_four_invalid_static
example : observe («dfn'FSQRT_S» (3,1,4) (state 0x40800000 0x42 0)) =
    (0xCAFE000000000000,0x40800000,66,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  change observe (signalException ExceptionType.Illegal_Instr (state 0x40800000 0x42 0)) = _
  decide +kernel

-- Original fsqrt_s_four_invalid_dynamic
example : observe («dfn'FSQRT_S» (3,1,7) (state 0x40800000 0x42 4)) =
    (0xCAFE000000000000,0x40800000,66,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  change observe (signalException ExceptionType.Illegal_Instr (state 0x40800000 0x42 4)) = _
  decide +kernel

-- Original fsqrt_s_negative_one_invalid_static
example : observe («dfn'FSQRT_S» (3,1,4) (state 0xbf800000 0x42 0)) =
    (0xCAFE000000000000,0xBF800000,66,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  change observe (signalException ExceptionType.Illegal_Instr (state 0xbf800000 0x42 0)) = _
  decide +kernel

-- Original fsqrt_s_negative_one_invalid_dynamic
example : observe («dfn'FSQRT_S» (3,1,7) (state 0xbf800000 0x42 4)) =
    (0xCAFE000000000000,0xBF800000,66,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  change observe (signalException ExceptionType.Illegal_Instr (state 0xbf800000 0x42 4)) = _
  decide +kernel

-- Original fsqrt_s_negative_zero_rte
example : observe («dfn'FSQRT_S» (3,1,0) (state 0x80000000 0x42 0)) =
    (0xCAFE000080000000,0x80000000,66,3,true,(some 0x80000000),false,true,
 0xBBBB000000000000,false) := by
  change observe (writeFPRS (3,0x80000000) (state 0x80000000 0x42 0)) = _
  decide +kernel

-- Original fsqrt_s_negative_zero_rtz
example : observe («dfn'FSQRT_S» (3,1,1) (state 0x80000000 0x42 0)) =
    (0xCAFE000080000000,0x80000000,66,3,true,(some 0x80000000),false,true,
 0xBBBB000000000000,false) := by
  change observe (writeFPRS (3,0x80000000) (state 0x80000000 0x42 0)) = _
  decide +kernel

-- Original fsqrt_s_negative_zero_down
example : observe («dfn'FSQRT_S» (3,1,2) (state 0x80000000 0x42 0)) =
    (0xCAFE000080000000,0x80000000,66,3,true,(some 0x80000000),false,true,
 0xBBBB000000000000,false) := by
  change observe (writeFPRS (3,0x80000000) (state 0x80000000 0x42 0)) = _
  decide +kernel

-- Original fsqrt_s_negative_zero_up
example : observe («dfn'FSQRT_S» (3,1,3) (state 0x80000000 0x42 0)) =
    (0xCAFE000080000000,0x80000000,66,3,true,(some 0x80000000),false,true,
 0xBBBB000000000000,false) := by
  change observe (writeFPRS (3,0x80000000) (state 0x80000000 0x42 0)) = _
  decide +kernel

-- Original fsqrt_s_negative_zero_dynamic_up
example : observe («dfn'FSQRT_S» (3,1,7) (state 0x80000000 0x42 3)) =
    (0xCAFE000080000000,0x80000000,66,3,true,(some 0x80000000),false,true,
 0xBBBB000000000000,false) := by
  change observe (writeFPRS (3,0x80000000) (state 0x80000000 0x42 3)) = _
  decide +kernel

-- Original fsqrt_s_negative_zero_invalid_static
example : observe («dfn'FSQRT_S» (3,1,4) (state 0x80000000 0x42 0)) =
    (0xCAFE000000000000,0x80000000,66,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  change observe (signalException ExceptionType.Illegal_Instr (state 0x80000000 0x42 0)) = _
  decide +kernel

-- Original fsqrt_s_negative_zero_invalid_dynamic
example : observe («dfn'FSQRT_S» (3,1,7) (state 0x80000000 0x42 4)) =
    (0xCAFE000000000000,0x80000000,66,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  change observe (signalException ExceptionType.Illegal_Instr (state 0x80000000 0x42 4)) = _
  decide +kernel

-- Original fsqrt_s_pinf_rte
example : observe («dfn'FSQRT_S» (3,1,0) (state 0x7f800000 0x42 0)) =
    (0xCAFE00007F800000,0x7F800000,66,3,true,(some 0x7F800000),false,true,
 0xBBBB000000000000,false) := by
  change observe (writeFPRS (3,0x7f800000) (state 0x7f800000 0x42 0)) = _
  decide +kernel

-- Original fsqrt_s_pinf_rtz
example : observe («dfn'FSQRT_S» (3,1,1) (state 0x7f800000 0x42 0)) =
    (0xCAFE00007F800000,0x7F800000,66,3,true,(some 0x7F800000),false,true,
 0xBBBB000000000000,false) := by
  change observe (writeFPRS (3,0x7f800000) (state 0x7f800000 0x42 0)) = _
  decide +kernel

-- Original fsqrt_s_pinf_down
example : observe («dfn'FSQRT_S» (3,1,2) (state 0x7f800000 0x42 0)) =
    (0xCAFE00007F800000,0x7F800000,66,3,true,(some 0x7F800000),false,true,
 0xBBBB000000000000,false) := by
  change observe (writeFPRS (3,0x7f800000) (state 0x7f800000 0x42 0)) = _
  decide +kernel

-- Original fsqrt_s_pinf_up
example : observe («dfn'FSQRT_S» (3,1,3) (state 0x7f800000 0x42 0)) =
    (0xCAFE00007F800000,0x7F800000,66,3,true,(some 0x7F800000),false,true,
 0xBBBB000000000000,false) := by
  change observe (writeFPRS (3,0x7f800000) (state 0x7f800000 0x42 0)) = _
  decide +kernel

-- Original fsqrt_s_pinf_dynamic_up
example : observe («dfn'FSQRT_S» (3,1,7) (state 0x7f800000 0x42 3)) =
    (0xCAFE00007F800000,0x7F800000,66,3,true,(some 0x7F800000),false,true,
 0xBBBB000000000000,false) := by
  change observe (writeFPRS (3,0x7f800000) (state 0x7f800000 0x42 3)) = _
  decide +kernel

-- Original fsqrt_s_pinf_invalid_static
example : observe («dfn'FSQRT_S» (3,1,4) (state 0x7f800000 0x42 0)) =
    (0xCAFE000000000000,0x7F800000,66,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  change observe (signalException ExceptionType.Illegal_Instr (state 0x7f800000 0x42 0)) = _
  decide +kernel

-- Original fsqrt_s_pinf_invalid_dynamic
example : observe («dfn'FSQRT_S» (3,1,7) (state 0x7f800000 0x42 4)) =
    (0xCAFE000000000000,0x7F800000,66,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  change observe (signalException ExceptionType.Illegal_Instr (state 0x7f800000 0x42 4)) = _
  decide +kernel

-- Original fsqrt_d_four_invalid_static
example : observe («dfn'FSQRT_D» (3,1,4) (state 0x4010000000000000 0x42 0)) =
    (0xCAFE000000000000,0x4010000000000000,66,0,false,(some 42),false,true,
 0xBBBB000000000000,true) := by
  change observe (signalException ExceptionType.Illegal_Instr (state 0x4010000000000000 0x42 0)) = _
  decide +kernel

-- Original fsqrt_d_four_invalid_dynamic
example : observe («dfn'FSQRT_D» (3,1,7) (state 0x4010000000000000 0x42 4)) =
    (0xCAFE000000000000,0x4010000000000000,66,0,false,(some 42),false,true,
 0xBBBB000000000000,true) := by
  change observe (signalException ExceptionType.Illegal_Instr (state 0x4010000000000000 0x42 4)) = _
  decide +kernel

-- Original fsqrt_d_negative_one_invalid_static
example : observe («dfn'FSQRT_D» (3,1,4) (state 0xbff0000000000000 0x42 0)) =
    (0xCAFE000000000000,0xBFF0000000000000,66,0,false,(some 42),false,true,
 0xBBBB000000000000,true) := by
  change observe (signalException ExceptionType.Illegal_Instr (state 0xbff0000000000000 0x42 0)) = _
  decide +kernel

-- Original fsqrt_d_negative_one_invalid_dynamic
example : observe («dfn'FSQRT_D» (3,1,7) (state 0xbff0000000000000 0x42 4)) =
    (0xCAFE000000000000,0xBFF0000000000000,66,0,false,(some 42),false,true,
 0xBBBB000000000000,true) := by
  change observe (signalException ExceptionType.Illegal_Instr (state 0xbff0000000000000 0x42 4)) = _
  decide +kernel

-- Original fsqrt_d_negative_zero_rte
example : observe («dfn'FSQRT_D» (3,1,0) (state 0x8000000000000000 0x42 0)) =
    (0x8000000000000000,0x8000000000000000,66,3,true,(some 0x8000000000000000),false,
 true,0xBBBB000000000000,false) := by
  change observe (writeFPRD (3,0x8000000000000000) (state 0x8000000000000000 0x42 0)) = _
  decide +kernel

-- Original fsqrt_d_negative_zero_rtz
example : observe («dfn'FSQRT_D» (3,1,1) (state 0x8000000000000000 0x42 0)) =
    (0x8000000000000000,0x8000000000000000,66,3,true,(some 0x8000000000000000),false,
 true,0xBBBB000000000000,false) := by
  change observe (writeFPRD (3,0x8000000000000000) (state 0x8000000000000000 0x42 0)) = _
  decide +kernel

-- Original fsqrt_d_negative_zero_down
example : observe («dfn'FSQRT_D» (3,1,2) (state 0x8000000000000000 0x42 0)) =
    (0x8000000000000000,0x8000000000000000,66,3,true,(some 0x8000000000000000),false,
 true,0xBBBB000000000000,false) := by
  change observe (writeFPRD (3,0x8000000000000000) (state 0x8000000000000000 0x42 0)) = _
  decide +kernel

-- Original fsqrt_d_negative_zero_up
example : observe («dfn'FSQRT_D» (3,1,3) (state 0x8000000000000000 0x42 0)) =
    (0x8000000000000000,0x8000000000000000,66,3,true,(some 0x8000000000000000),false,
 true,0xBBBB000000000000,false) := by
  change observe (writeFPRD (3,0x8000000000000000) (state 0x8000000000000000 0x42 0)) = _
  decide +kernel

-- Original fsqrt_d_negative_zero_dynamic_up
example : observe («dfn'FSQRT_D» (3,1,7) (state 0x8000000000000000 0x42 3)) =
    (0x8000000000000000,0x8000000000000000,66,3,true,(some 0x8000000000000000),false,
 true,0xBBBB000000000000,false) := by
  change observe (writeFPRD (3,0x8000000000000000) (state 0x8000000000000000 0x42 3)) = _
  decide +kernel

-- Original fsqrt_d_negative_zero_invalid_static
example : observe («dfn'FSQRT_D» (3,1,4) (state 0x8000000000000000 0x42 0)) =
    (0xCAFE000000000000,0x8000000000000000,66,0,false,(some 42),false,true,
 0xBBBB000000000000,true) := by
  change observe (signalException ExceptionType.Illegal_Instr (state 0x8000000000000000 0x42 0)) = _
  decide +kernel

-- Original fsqrt_d_negative_zero_invalid_dynamic
example : observe («dfn'FSQRT_D» (3,1,7) (state 0x8000000000000000 0x42 4)) =
    (0xCAFE000000000000,0x8000000000000000,66,0,false,(some 42),false,true,
 0xBBBB000000000000,true) := by
  change observe (signalException ExceptionType.Illegal_Instr (state 0x8000000000000000 0x42 4)) = _
  decide +kernel

-- Original fsqrt_d_pinf_rte
example : observe («dfn'FSQRT_D» (3,1,0) (state 0x7ff0000000000000 0x42 0)) =
    (0x7FF0000000000000,0x7FF0000000000000,66,3,true,(some 0x7FF0000000000000),false,
 true,0xBBBB000000000000,false) := by
  change observe (writeFPRD (3,0x7ff0000000000000) (state 0x7ff0000000000000 0x42 0)) = _
  decide +kernel

-- Original fsqrt_d_pinf_rtz
example : observe («dfn'FSQRT_D» (3,1,1) (state 0x7ff0000000000000 0x42 0)) =
    (0x7FF0000000000000,0x7FF0000000000000,66,3,true,(some 0x7FF0000000000000),false,
 true,0xBBBB000000000000,false) := by
  change observe (writeFPRD (3,0x7ff0000000000000) (state 0x7ff0000000000000 0x42 0)) = _
  decide +kernel

-- Original fsqrt_d_pinf_down
example : observe («dfn'FSQRT_D» (3,1,2) (state 0x7ff0000000000000 0x42 0)) =
    (0x7FF0000000000000,0x7FF0000000000000,66,3,true,(some 0x7FF0000000000000),false,
 true,0xBBBB000000000000,false) := by
  change observe (writeFPRD (3,0x7ff0000000000000) (state 0x7ff0000000000000 0x42 0)) = _
  decide +kernel

-- Original fsqrt_d_pinf_up
example : observe («dfn'FSQRT_D» (3,1,3) (state 0x7ff0000000000000 0x42 0)) =
    (0x7FF0000000000000,0x7FF0000000000000,66,3,true,(some 0x7FF0000000000000),false,
 true,0xBBBB000000000000,false) := by
  change observe (writeFPRD (3,0x7ff0000000000000) (state 0x7ff0000000000000 0x42 0)) = _
  decide +kernel

-- Original fsqrt_d_pinf_dynamic_up
example : observe («dfn'FSQRT_D» (3,1,7) (state 0x7ff0000000000000 0x42 3)) =
    (0x7FF0000000000000,0x7FF0000000000000,66,3,true,(some 0x7FF0000000000000),false,
 true,0xBBBB000000000000,false) := by
  change observe (writeFPRD (3,0x7ff0000000000000) (state 0x7ff0000000000000 0x42 3)) = _
  decide +kernel

-- Original fsqrt_d_pinf_invalid_static
example : observe («dfn'FSQRT_D» (3,1,4) (state 0x7ff0000000000000 0x42 0)) =
    (0xCAFE000000000000,0x7FF0000000000000,66,0,false,(some 42),false,true,
 0xBBBB000000000000,true) := by
  change observe (signalException ExceptionType.Illegal_Instr (state 0x7ff0000000000000 0x42 0)) = _
  decide +kernel

-- Original fsqrt_d_pinf_invalid_dynamic
example : observe («dfn'FSQRT_D» (3,1,7) (state 0x7ff0000000000000 0x42 4)) =
    (0xCAFE000000000000,0x7FF0000000000000,66,0,false,(some 42),false,true,
 0xBBBB000000000000,true) := by
  change observe (signalException ExceptionType.Illegal_Instr (state 0x7ff0000000000000 0x42 4)) = _
  decide +kernel

end Flapjack.Test.L3RiscvSqrtParity
