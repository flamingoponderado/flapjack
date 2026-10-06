import Flapjack.RiscV.L3.Defs.ImmediateShift

set_option maxRecDepth 20000
namespace Flapjack.Test.L3ImmediateShiftParity
open Flapjack.RiscV.L3
private def fixture (s : riscv_state) (mode : BitVec 2) (lhs : BitVec 64) : riscv_state :=
 {s with procID := 7, c_MCSR := fun id => {s.c_MCSR id with mcpuid := {(s.c_MCSR id).mcpuid with ArchBase := mode}}, c_gpr := fun id r => if r = 1 then lhs else s.c_gpr id r}

-- immediate_shift_SLLI_0_0_0
example (s : riscv_state) : «dfn'SLLI» (0,1,0) (fixture s 0 9223372036854775808) =
 (let t := fixture s 0 9223372036854775808; t) := by
  change «write'GPR» (((9223372036854775808 : BitVec 64) <<< (0 : BitVec 6).toNat), 0) (fixture s 0 9223372036854775808) = _
  have numeric : (((9223372036854775808 : BitVec 64) <<< (0 : BitVec 6).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_0_0_1
example (s : riscv_state) : «dfn'SLLI» (1,1,0) (fixture s 0 9223372036854775808) =
 (let t := fixture s 0 9223372036854775808; {t with c_gpr := holUpdate 7 (holUpdate 1 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775808 : BitVec 64) <<< (0 : BitVec 6).toNat), 1) (fixture s 0 9223372036854775808) = _
  have numeric : (((9223372036854775808 : BitVec 64) <<< (0 : BitVec 6).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_0_0_7
example (s : riscv_state) : «dfn'SLLI» (7,1,0) (fixture s 0 9223372036854775808) =
 (let t := fixture s 0 9223372036854775808; {t with c_gpr := holUpdate 7 (holUpdate 7 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775808 : BitVec 64) <<< (0 : BitVec 6).toNat), 7) (fixture s 0 9223372036854775808) = _
  have numeric : (((9223372036854775808 : BitVec 64) <<< (0 : BitVec 6).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_0_1_0
example (s : riscv_state) : «dfn'SLLI» (0,1,1) (fixture s 0 2147483649) =
 (let t := fixture s 0 2147483649; t) := by
  change «write'GPR» (((2147483649 : BitVec 64) <<< (1 : BitVec 6).toNat), 0) (fixture s 0 2147483649) = _
  have numeric : (((2147483649 : BitVec 64) <<< (1 : BitVec 6).toNat)) = (4294967298 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_0_1_1
example (s : riscv_state) : «dfn'SLLI» (1,1,1) (fixture s 0 2147483649) =
 (let t := fixture s 0 2147483649; {t with c_gpr := holUpdate 7 (holUpdate 1 4294967298 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((2147483649 : BitVec 64) <<< (1 : BitVec 6).toNat), 1) (fixture s 0 2147483649) = _
  have numeric : (((2147483649 : BitVec 64) <<< (1 : BitVec 6).toNat)) = (4294967298 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_0_1_7
example (s : riscv_state) : «dfn'SLLI» (7,1,1) (fixture s 0 2147483649) =
 (let t := fixture s 0 2147483649; {t with c_gpr := holUpdate 7 (holUpdate 7 4294967298 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((2147483649 : BitVec 64) <<< (1 : BitVec 6).toNat), 7) (fixture s 0 2147483649) = _
  have numeric : (((2147483649 : BitVec 64) <<< (1 : BitVec 6).toNat)) = (4294967298 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_0_2_0
example (s : riscv_state) : «dfn'SLLI» (0,1,31) (fixture s 0 4294967297) =
 (let t := fixture s 0 4294967297; t) := by
  change «write'GPR» (((4294967297 : BitVec 64) <<< (31 : BitVec 6).toNat), 0) (fixture s 0 4294967297) = _
  have numeric : (((4294967297 : BitVec 64) <<< (31 : BitVec 6).toNat)) = (9223372039002259456 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_0_2_1
example (s : riscv_state) : «dfn'SLLI» (1,1,31) (fixture s 0 4294967297) =
 (let t := fixture s 0 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 1 9223372039002259456 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((4294967297 : BitVec 64) <<< (31 : BitVec 6).toNat), 1) (fixture s 0 4294967297) = _
  have numeric : (((4294967297 : BitVec 64) <<< (31 : BitVec 6).toNat)) = (9223372039002259456 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_0_2_7
example (s : riscv_state) : «dfn'SLLI» (7,1,31) (fixture s 0 4294967297) =
 (let t := fixture s 0 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 7 9223372039002259456 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((4294967297 : BitVec 64) <<< (31 : BitVec 6).toNat), 7) (fixture s 0 4294967297) = _
  have numeric : (((4294967297 : BitVec 64) <<< (31 : BitVec 6).toNat)) = (9223372039002259456 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_0_3_0
example (s : riscv_state) : «dfn'SLLI» (0,1,32) (fixture s 0 18446744073709551615) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615) := by rfl

-- immediate_shift_SLLI_0_3_1
example (s : riscv_state) : «dfn'SLLI» (1,1,32) (fixture s 0 18446744073709551615) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615) := by rfl

-- immediate_shift_SLLI_0_3_7
example (s : riscv_state) : «dfn'SLLI» (7,1,32) (fixture s 0 18446744073709551615) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615) := by rfl

-- immediate_shift_SLLI_0_4_0
example (s : riscv_state) : «dfn'SLLI» (0,1,33) (fixture s 0 2147483648) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483648) := by rfl

-- immediate_shift_SLLI_0_4_1
example (s : riscv_state) : «dfn'SLLI» (1,1,33) (fixture s 0 2147483648) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483648) := by rfl

-- immediate_shift_SLLI_0_4_7
example (s : riscv_state) : «dfn'SLLI» (7,1,33) (fixture s 0 2147483648) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483648) := by rfl

-- immediate_shift_SLLI_0_5_0
example (s : riscv_state) : «dfn'SLLI» (0,1,63) (fixture s 0 4294967296) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967296) := by rfl

-- immediate_shift_SLLI_0_5_1
example (s : riscv_state) : «dfn'SLLI» (1,1,63) (fixture s 0 4294967296) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967296) := by rfl

-- immediate_shift_SLLI_0_5_7
example (s : riscv_state) : «dfn'SLLI» (7,1,63) (fixture s 0 4294967296) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967296) := by rfl

-- immediate_shift_SLLI_0_6_0
example (s : riscv_state) : «dfn'SLLI» (0,1,15) (fixture s 0 9223372036854775809) =
 (let t := fixture s 0 9223372036854775809; t) := by
  change «write'GPR» (((9223372036854775809 : BitVec 64) <<< (15 : BitVec 6).toNat), 0) (fixture s 0 9223372036854775809) = _
  have numeric : (((9223372036854775809 : BitVec 64) <<< (15 : BitVec 6).toNat)) = (32768 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_0_6_1
example (s : riscv_state) : «dfn'SLLI» (1,1,15) (fixture s 0 9223372036854775809) =
 (let t := fixture s 0 9223372036854775809; {t with c_gpr := holUpdate 7 (holUpdate 1 32768 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775809 : BitVec 64) <<< (15 : BitVec 6).toNat), 1) (fixture s 0 9223372036854775809) = _
  have numeric : (((9223372036854775809 : BitVec 64) <<< (15 : BitVec 6).toNat)) = (32768 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_0_6_7
example (s : riscv_state) : «dfn'SLLI» (7,1,15) (fixture s 0 9223372036854775809) =
 (let t := fixture s 0 9223372036854775809; {t with c_gpr := holUpdate 7 (holUpdate 7 32768 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775809 : BitVec 64) <<< (15 : BitVec 6).toNat), 7) (fixture s 0 9223372036854775809) = _
  have numeric : (((9223372036854775809 : BitVec 64) <<< (15 : BitVec 6).toNat)) = (32768 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_0_7_0
example (s : riscv_state) : «dfn'SLLI» (0,1,30) (fixture s 0 18446744073709551615) =
 (let t := fixture s 0 18446744073709551615; t) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) <<< (30 : BitVec 6).toNat), 0) (fixture s 0 18446744073709551615) = _
  have numeric : (((18446744073709551615 : BitVec 64) <<< (30 : BitVec 6).toNat)) = (18446744072635809792 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_0_7_1
example (s : riscv_state) : «dfn'SLLI» (1,1,30) (fixture s 0 18446744073709551615) =
 (let t := fixture s 0 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744072635809792 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) <<< (30 : BitVec 6).toNat), 1) (fixture s 0 18446744073709551615) = _
  have numeric : (((18446744073709551615 : BitVec 64) <<< (30 : BitVec 6).toNat)) = (18446744072635809792 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_0_7_7
example (s : riscv_state) : «dfn'SLLI» (7,1,30) (fixture s 0 18446744073709551615) =
 (let t := fixture s 0 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744072635809792 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) <<< (30 : BitVec 6).toNat), 7) (fixture s 0 18446744073709551615) = _
  have numeric : (((18446744073709551615 : BitVec 64) <<< (30 : BitVec 6).toNat)) = (18446744072635809792 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_0_8_0
example (s : riscv_state) : «dfn'SLLI» (0,0,31) (fixture s 0 17) =
 (let t := fixture s 0 17; t) := by
  change «write'GPR» (((0 : BitVec 64) <<< (31 : BitVec 6).toNat), 0) (fixture s 0 17) = _
  have numeric : (((0 : BitVec 64) <<< (31 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_0_8_1
example (s : riscv_state) : «dfn'SLLI» (1,0,31) (fixture s 0 17) =
 (let t := fixture s 0 17; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((0 : BitVec 64) <<< (31 : BitVec 6).toNat), 1) (fixture s 0 17) = _
  have numeric : (((0 : BitVec 64) <<< (31 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_0_8_7
example (s : riscv_state) : «dfn'SLLI» (7,0,31) (fixture s 0 17) =
 (let t := fixture s 0 17; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((0 : BitVec 64) <<< (31 : BitVec 6).toNat), 7) (fixture s 0 17) = _
  have numeric : (((0 : BitVec 64) <<< (31 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_0_9_0
example (s : riscv_state) : «dfn'SLLI» (0,0,1) (fixture s 0 18446744073709551615) =
 (let t := fixture s 0 18446744073709551615; t) := by
  change «write'GPR» (((0 : BitVec 64) <<< (1 : BitVec 6).toNat), 0) (fixture s 0 18446744073709551615) = _
  have numeric : (((0 : BitVec 64) <<< (1 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_0_9_1
example (s : riscv_state) : «dfn'SLLI» (1,0,1) (fixture s 0 18446744073709551615) =
 (let t := fixture s 0 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((0 : BitVec 64) <<< (1 : BitVec 6).toNat), 1) (fixture s 0 18446744073709551615) = _
  have numeric : (((0 : BitVec 64) <<< (1 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_0_9_7
example (s : riscv_state) : «dfn'SLLI» (7,0,1) (fixture s 0 18446744073709551615) =
 (let t := fixture s 0 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((0 : BitVec 64) <<< (1 : BitVec 6).toNat), 7) (fixture s 0 18446744073709551615) = _
  have numeric : (((0 : BitVec 64) <<< (1 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_2_0_0
example (s : riscv_state) : «dfn'SLLI» (0,1,0) (fixture s 2 9223372036854775808) =
 (let t := fixture s 2 9223372036854775808; t) := by
  change «write'GPR» (((9223372036854775808 : BitVec 64) <<< (0 : BitVec 6).toNat), 0) (fixture s 2 9223372036854775808) = _
  have numeric : (((9223372036854775808 : BitVec 64) <<< (0 : BitVec 6).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_2_0_1
example (s : riscv_state) : «dfn'SLLI» (1,1,0) (fixture s 2 9223372036854775808) =
 (let t := fixture s 2 9223372036854775808; {t with c_gpr := holUpdate 7 (holUpdate 1 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775808 : BitVec 64) <<< (0 : BitVec 6).toNat), 1) (fixture s 2 9223372036854775808) = _
  have numeric : (((9223372036854775808 : BitVec 64) <<< (0 : BitVec 6).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_2_0_7
example (s : riscv_state) : «dfn'SLLI» (7,1,0) (fixture s 2 9223372036854775808) =
 (let t := fixture s 2 9223372036854775808; {t with c_gpr := holUpdate 7 (holUpdate 7 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775808 : BitVec 64) <<< (0 : BitVec 6).toNat), 7) (fixture s 2 9223372036854775808) = _
  have numeric : (((9223372036854775808 : BitVec 64) <<< (0 : BitVec 6).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_2_1_0
example (s : riscv_state) : «dfn'SLLI» (0,1,1) (fixture s 2 2147483649) =
 (let t := fixture s 2 2147483649; t) := by
  change «write'GPR» (((2147483649 : BitVec 64) <<< (1 : BitVec 6).toNat), 0) (fixture s 2 2147483649) = _
  have numeric : (((2147483649 : BitVec 64) <<< (1 : BitVec 6).toNat)) = (4294967298 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_2_1_1
example (s : riscv_state) : «dfn'SLLI» (1,1,1) (fixture s 2 2147483649) =
 (let t := fixture s 2 2147483649; {t with c_gpr := holUpdate 7 (holUpdate 1 4294967298 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((2147483649 : BitVec 64) <<< (1 : BitVec 6).toNat), 1) (fixture s 2 2147483649) = _
  have numeric : (((2147483649 : BitVec 64) <<< (1 : BitVec 6).toNat)) = (4294967298 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_2_1_7
example (s : riscv_state) : «dfn'SLLI» (7,1,1) (fixture s 2 2147483649) =
 (let t := fixture s 2 2147483649; {t with c_gpr := holUpdate 7 (holUpdate 7 4294967298 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((2147483649 : BitVec 64) <<< (1 : BitVec 6).toNat), 7) (fixture s 2 2147483649) = _
  have numeric : (((2147483649 : BitVec 64) <<< (1 : BitVec 6).toNat)) = (4294967298 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_2_2_0
example (s : riscv_state) : «dfn'SLLI» (0,1,31) (fixture s 2 4294967297) =
 (let t := fixture s 2 4294967297; t) := by
  change «write'GPR» (((4294967297 : BitVec 64) <<< (31 : BitVec 6).toNat), 0) (fixture s 2 4294967297) = _
  have numeric : (((4294967297 : BitVec 64) <<< (31 : BitVec 6).toNat)) = (9223372039002259456 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_2_2_1
example (s : riscv_state) : «dfn'SLLI» (1,1,31) (fixture s 2 4294967297) =
 (let t := fixture s 2 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 1 9223372039002259456 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((4294967297 : BitVec 64) <<< (31 : BitVec 6).toNat), 1) (fixture s 2 4294967297) = _
  have numeric : (((4294967297 : BitVec 64) <<< (31 : BitVec 6).toNat)) = (9223372039002259456 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_2_2_7
example (s : riscv_state) : «dfn'SLLI» (7,1,31) (fixture s 2 4294967297) =
 (let t := fixture s 2 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 7 9223372039002259456 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((4294967297 : BitVec 64) <<< (31 : BitVec 6).toNat), 7) (fixture s 2 4294967297) = _
  have numeric : (((4294967297 : BitVec 64) <<< (31 : BitVec 6).toNat)) = (9223372039002259456 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_2_3_0
example (s : riscv_state) : «dfn'SLLI» (0,1,32) (fixture s 2 18446744073709551615) =
 (let t := fixture s 2 18446744073709551615; t) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) <<< (32 : BitVec 6).toNat), 0) (fixture s 2 18446744073709551615) = _
  have numeric : (((18446744073709551615 : BitVec 64) <<< (32 : BitVec 6).toNat)) = (18446744069414584320 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_2_3_1
example (s : riscv_state) : «dfn'SLLI» (1,1,32) (fixture s 2 18446744073709551615) =
 (let t := fixture s 2 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744069414584320 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) <<< (32 : BitVec 6).toNat), 1) (fixture s 2 18446744073709551615) = _
  have numeric : (((18446744073709551615 : BitVec 64) <<< (32 : BitVec 6).toNat)) = (18446744069414584320 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_2_3_7
example (s : riscv_state) : «dfn'SLLI» (7,1,32) (fixture s 2 18446744073709551615) =
 (let t := fixture s 2 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744069414584320 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) <<< (32 : BitVec 6).toNat), 7) (fixture s 2 18446744073709551615) = _
  have numeric : (((18446744073709551615 : BitVec 64) <<< (32 : BitVec 6).toNat)) = (18446744069414584320 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_2_4_0
example (s : riscv_state) : «dfn'SLLI» (0,1,33) (fixture s 2 2147483648) =
 (let t := fixture s 2 2147483648; t) := by
  change «write'GPR» (((2147483648 : BitVec 64) <<< (33 : BitVec 6).toNat), 0) (fixture s 2 2147483648) = _
  have numeric : (((2147483648 : BitVec 64) <<< (33 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_2_4_1
example (s : riscv_state) : «dfn'SLLI» (1,1,33) (fixture s 2 2147483648) =
 (let t := fixture s 2 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((2147483648 : BitVec 64) <<< (33 : BitVec 6).toNat), 1) (fixture s 2 2147483648) = _
  have numeric : (((2147483648 : BitVec 64) <<< (33 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_2_4_7
example (s : riscv_state) : «dfn'SLLI» (7,1,33) (fixture s 2 2147483648) =
 (let t := fixture s 2 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((2147483648 : BitVec 64) <<< (33 : BitVec 6).toNat), 7) (fixture s 2 2147483648) = _
  have numeric : (((2147483648 : BitVec 64) <<< (33 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_2_5_0
example (s : riscv_state) : «dfn'SLLI» (0,1,63) (fixture s 2 4294967296) =
 (let t := fixture s 2 4294967296; t) := by
  change «write'GPR» (((4294967296 : BitVec 64) <<< (63 : BitVec 6).toNat), 0) (fixture s 2 4294967296) = _
  have numeric : (((4294967296 : BitVec 64) <<< (63 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_2_5_1
example (s : riscv_state) : «dfn'SLLI» (1,1,63) (fixture s 2 4294967296) =
 (let t := fixture s 2 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((4294967296 : BitVec 64) <<< (63 : BitVec 6).toNat), 1) (fixture s 2 4294967296) = _
  have numeric : (((4294967296 : BitVec 64) <<< (63 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_2_5_7
example (s : riscv_state) : «dfn'SLLI» (7,1,63) (fixture s 2 4294967296) =
 (let t := fixture s 2 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((4294967296 : BitVec 64) <<< (63 : BitVec 6).toNat), 7) (fixture s 2 4294967296) = _
  have numeric : (((4294967296 : BitVec 64) <<< (63 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_2_6_0
example (s : riscv_state) : «dfn'SLLI» (0,1,15) (fixture s 2 9223372036854775809) =
 (let t := fixture s 2 9223372036854775809; t) := by
  change «write'GPR» (((9223372036854775809 : BitVec 64) <<< (15 : BitVec 6).toNat), 0) (fixture s 2 9223372036854775809) = _
  have numeric : (((9223372036854775809 : BitVec 64) <<< (15 : BitVec 6).toNat)) = (32768 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_2_6_1
example (s : riscv_state) : «dfn'SLLI» (1,1,15) (fixture s 2 9223372036854775809) =
 (let t := fixture s 2 9223372036854775809; {t with c_gpr := holUpdate 7 (holUpdate 1 32768 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775809 : BitVec 64) <<< (15 : BitVec 6).toNat), 1) (fixture s 2 9223372036854775809) = _
  have numeric : (((9223372036854775809 : BitVec 64) <<< (15 : BitVec 6).toNat)) = (32768 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_2_6_7
example (s : riscv_state) : «dfn'SLLI» (7,1,15) (fixture s 2 9223372036854775809) =
 (let t := fixture s 2 9223372036854775809; {t with c_gpr := holUpdate 7 (holUpdate 7 32768 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775809 : BitVec 64) <<< (15 : BitVec 6).toNat), 7) (fixture s 2 9223372036854775809) = _
  have numeric : (((9223372036854775809 : BitVec 64) <<< (15 : BitVec 6).toNat)) = (32768 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_2_7_0
example (s : riscv_state) : «dfn'SLLI» (0,1,30) (fixture s 2 18446744073709551615) =
 (let t := fixture s 2 18446744073709551615; t) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) <<< (30 : BitVec 6).toNat), 0) (fixture s 2 18446744073709551615) = _
  have numeric : (((18446744073709551615 : BitVec 64) <<< (30 : BitVec 6).toNat)) = (18446744072635809792 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_2_7_1
example (s : riscv_state) : «dfn'SLLI» (1,1,30) (fixture s 2 18446744073709551615) =
 (let t := fixture s 2 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744072635809792 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) <<< (30 : BitVec 6).toNat), 1) (fixture s 2 18446744073709551615) = _
  have numeric : (((18446744073709551615 : BitVec 64) <<< (30 : BitVec 6).toNat)) = (18446744072635809792 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_2_7_7
example (s : riscv_state) : «dfn'SLLI» (7,1,30) (fixture s 2 18446744073709551615) =
 (let t := fixture s 2 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744072635809792 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) <<< (30 : BitVec 6).toNat), 7) (fixture s 2 18446744073709551615) = _
  have numeric : (((18446744073709551615 : BitVec 64) <<< (30 : BitVec 6).toNat)) = (18446744072635809792 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_2_8_0
example (s : riscv_state) : «dfn'SLLI» (0,0,31) (fixture s 2 17) =
 (let t := fixture s 2 17; t) := by
  change «write'GPR» (((0 : BitVec 64) <<< (31 : BitVec 6).toNat), 0) (fixture s 2 17) = _
  have numeric : (((0 : BitVec 64) <<< (31 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_2_8_1
example (s : riscv_state) : «dfn'SLLI» (1,0,31) (fixture s 2 17) =
 (let t := fixture s 2 17; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((0 : BitVec 64) <<< (31 : BitVec 6).toNat), 1) (fixture s 2 17) = _
  have numeric : (((0 : BitVec 64) <<< (31 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_2_8_7
example (s : riscv_state) : «dfn'SLLI» (7,0,31) (fixture s 2 17) =
 (let t := fixture s 2 17; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((0 : BitVec 64) <<< (31 : BitVec 6).toNat), 7) (fixture s 2 17) = _
  have numeric : (((0 : BitVec 64) <<< (31 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_2_9_0
example (s : riscv_state) : «dfn'SLLI» (0,0,1) (fixture s 2 18446744073709551615) =
 (let t := fixture s 2 18446744073709551615; t) := by
  change «write'GPR» (((0 : BitVec 64) <<< (1 : BitVec 6).toNat), 0) (fixture s 2 18446744073709551615) = _
  have numeric : (((0 : BitVec 64) <<< (1 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_2_9_1
example (s : riscv_state) : «dfn'SLLI» (1,0,1) (fixture s 2 18446744073709551615) =
 (let t := fixture s 2 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((0 : BitVec 64) <<< (1 : BitVec 6).toNat), 1) (fixture s 2 18446744073709551615) = _
  have numeric : (((0 : BitVec 64) <<< (1 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_2_9_7
example (s : riscv_state) : «dfn'SLLI» (7,0,1) (fixture s 2 18446744073709551615) =
 (let t := fixture s 2 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((0 : BitVec 64) <<< (1 : BitVec 6).toNat), 7) (fixture s 2 18446744073709551615) = _
  have numeric : (((0 : BitVec 64) <<< (1 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_3_0_0
example (s : riscv_state) : «dfn'SLLI» (0,1,0) (fixture s 3 9223372036854775808) =
 (let t := fixture s 3 9223372036854775808; t) := by
  change «write'GPR» (((9223372036854775808 : BitVec 64) <<< (0 : BitVec 6).toNat), 0) (fixture s 3 9223372036854775808) = _
  have numeric : (((9223372036854775808 : BitVec 64) <<< (0 : BitVec 6).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_3_0_1
example (s : riscv_state) : «dfn'SLLI» (1,1,0) (fixture s 3 9223372036854775808) =
 (let t := fixture s 3 9223372036854775808; {t with c_gpr := holUpdate 7 (holUpdate 1 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775808 : BitVec 64) <<< (0 : BitVec 6).toNat), 1) (fixture s 3 9223372036854775808) = _
  have numeric : (((9223372036854775808 : BitVec 64) <<< (0 : BitVec 6).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_3_0_7
example (s : riscv_state) : «dfn'SLLI» (7,1,0) (fixture s 3 9223372036854775808) =
 (let t := fixture s 3 9223372036854775808; {t with c_gpr := holUpdate 7 (holUpdate 7 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775808 : BitVec 64) <<< (0 : BitVec 6).toNat), 7) (fixture s 3 9223372036854775808) = _
  have numeric : (((9223372036854775808 : BitVec 64) <<< (0 : BitVec 6).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_3_1_0
example (s : riscv_state) : «dfn'SLLI» (0,1,1) (fixture s 3 2147483649) =
 (let t := fixture s 3 2147483649; t) := by
  change «write'GPR» (((2147483649 : BitVec 64) <<< (1 : BitVec 6).toNat), 0) (fixture s 3 2147483649) = _
  have numeric : (((2147483649 : BitVec 64) <<< (1 : BitVec 6).toNat)) = (4294967298 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_3_1_1
example (s : riscv_state) : «dfn'SLLI» (1,1,1) (fixture s 3 2147483649) =
 (let t := fixture s 3 2147483649; {t with c_gpr := holUpdate 7 (holUpdate 1 4294967298 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((2147483649 : BitVec 64) <<< (1 : BitVec 6).toNat), 1) (fixture s 3 2147483649) = _
  have numeric : (((2147483649 : BitVec 64) <<< (1 : BitVec 6).toNat)) = (4294967298 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_3_1_7
example (s : riscv_state) : «dfn'SLLI» (7,1,1) (fixture s 3 2147483649) =
 (let t := fixture s 3 2147483649; {t with c_gpr := holUpdate 7 (holUpdate 7 4294967298 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((2147483649 : BitVec 64) <<< (1 : BitVec 6).toNat), 7) (fixture s 3 2147483649) = _
  have numeric : (((2147483649 : BitVec 64) <<< (1 : BitVec 6).toNat)) = (4294967298 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_3_2_0
example (s : riscv_state) : «dfn'SLLI» (0,1,31) (fixture s 3 4294967297) =
 (let t := fixture s 3 4294967297; t) := by
  change «write'GPR» (((4294967297 : BitVec 64) <<< (31 : BitVec 6).toNat), 0) (fixture s 3 4294967297) = _
  have numeric : (((4294967297 : BitVec 64) <<< (31 : BitVec 6).toNat)) = (9223372039002259456 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_3_2_1
example (s : riscv_state) : «dfn'SLLI» (1,1,31) (fixture s 3 4294967297) =
 (let t := fixture s 3 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 1 9223372039002259456 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((4294967297 : BitVec 64) <<< (31 : BitVec 6).toNat), 1) (fixture s 3 4294967297) = _
  have numeric : (((4294967297 : BitVec 64) <<< (31 : BitVec 6).toNat)) = (9223372039002259456 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_3_2_7
example (s : riscv_state) : «dfn'SLLI» (7,1,31) (fixture s 3 4294967297) =
 (let t := fixture s 3 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 7 9223372039002259456 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((4294967297 : BitVec 64) <<< (31 : BitVec 6).toNat), 7) (fixture s 3 4294967297) = _
  have numeric : (((4294967297 : BitVec 64) <<< (31 : BitVec 6).toNat)) = (9223372039002259456 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_3_3_0
example (s : riscv_state) : «dfn'SLLI» (0,1,32) (fixture s 3 18446744073709551615) =
 (let t := fixture s 3 18446744073709551615; t) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) <<< (32 : BitVec 6).toNat), 0) (fixture s 3 18446744073709551615) = _
  have numeric : (((18446744073709551615 : BitVec 64) <<< (32 : BitVec 6).toNat)) = (18446744069414584320 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_3_3_1
example (s : riscv_state) : «dfn'SLLI» (1,1,32) (fixture s 3 18446744073709551615) =
 (let t := fixture s 3 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744069414584320 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) <<< (32 : BitVec 6).toNat), 1) (fixture s 3 18446744073709551615) = _
  have numeric : (((18446744073709551615 : BitVec 64) <<< (32 : BitVec 6).toNat)) = (18446744069414584320 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_3_3_7
example (s : riscv_state) : «dfn'SLLI» (7,1,32) (fixture s 3 18446744073709551615) =
 (let t := fixture s 3 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744069414584320 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) <<< (32 : BitVec 6).toNat), 7) (fixture s 3 18446744073709551615) = _
  have numeric : (((18446744073709551615 : BitVec 64) <<< (32 : BitVec 6).toNat)) = (18446744069414584320 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_3_4_0
example (s : riscv_state) : «dfn'SLLI» (0,1,33) (fixture s 3 2147483648) =
 (let t := fixture s 3 2147483648; t) := by
  change «write'GPR» (((2147483648 : BitVec 64) <<< (33 : BitVec 6).toNat), 0) (fixture s 3 2147483648) = _
  have numeric : (((2147483648 : BitVec 64) <<< (33 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_3_4_1
example (s : riscv_state) : «dfn'SLLI» (1,1,33) (fixture s 3 2147483648) =
 (let t := fixture s 3 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((2147483648 : BitVec 64) <<< (33 : BitVec 6).toNat), 1) (fixture s 3 2147483648) = _
  have numeric : (((2147483648 : BitVec 64) <<< (33 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_3_4_7
example (s : riscv_state) : «dfn'SLLI» (7,1,33) (fixture s 3 2147483648) =
 (let t := fixture s 3 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((2147483648 : BitVec 64) <<< (33 : BitVec 6).toNat), 7) (fixture s 3 2147483648) = _
  have numeric : (((2147483648 : BitVec 64) <<< (33 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_3_5_0
example (s : riscv_state) : «dfn'SLLI» (0,1,63) (fixture s 3 4294967296) =
 (let t := fixture s 3 4294967296; t) := by
  change «write'GPR» (((4294967296 : BitVec 64) <<< (63 : BitVec 6).toNat), 0) (fixture s 3 4294967296) = _
  have numeric : (((4294967296 : BitVec 64) <<< (63 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_3_5_1
example (s : riscv_state) : «dfn'SLLI» (1,1,63) (fixture s 3 4294967296) =
 (let t := fixture s 3 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((4294967296 : BitVec 64) <<< (63 : BitVec 6).toNat), 1) (fixture s 3 4294967296) = _
  have numeric : (((4294967296 : BitVec 64) <<< (63 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_3_5_7
example (s : riscv_state) : «dfn'SLLI» (7,1,63) (fixture s 3 4294967296) =
 (let t := fixture s 3 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((4294967296 : BitVec 64) <<< (63 : BitVec 6).toNat), 7) (fixture s 3 4294967296) = _
  have numeric : (((4294967296 : BitVec 64) <<< (63 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_3_6_0
example (s : riscv_state) : «dfn'SLLI» (0,1,15) (fixture s 3 9223372036854775809) =
 (let t := fixture s 3 9223372036854775809; t) := by
  change «write'GPR» (((9223372036854775809 : BitVec 64) <<< (15 : BitVec 6).toNat), 0) (fixture s 3 9223372036854775809) = _
  have numeric : (((9223372036854775809 : BitVec 64) <<< (15 : BitVec 6).toNat)) = (32768 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_3_6_1
example (s : riscv_state) : «dfn'SLLI» (1,1,15) (fixture s 3 9223372036854775809) =
 (let t := fixture s 3 9223372036854775809; {t with c_gpr := holUpdate 7 (holUpdate 1 32768 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775809 : BitVec 64) <<< (15 : BitVec 6).toNat), 1) (fixture s 3 9223372036854775809) = _
  have numeric : (((9223372036854775809 : BitVec 64) <<< (15 : BitVec 6).toNat)) = (32768 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_3_6_7
example (s : riscv_state) : «dfn'SLLI» (7,1,15) (fixture s 3 9223372036854775809) =
 (let t := fixture s 3 9223372036854775809; {t with c_gpr := holUpdate 7 (holUpdate 7 32768 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775809 : BitVec 64) <<< (15 : BitVec 6).toNat), 7) (fixture s 3 9223372036854775809) = _
  have numeric : (((9223372036854775809 : BitVec 64) <<< (15 : BitVec 6).toNat)) = (32768 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_3_7_0
example (s : riscv_state) : «dfn'SLLI» (0,1,30) (fixture s 3 18446744073709551615) =
 (let t := fixture s 3 18446744073709551615; t) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) <<< (30 : BitVec 6).toNat), 0) (fixture s 3 18446744073709551615) = _
  have numeric : (((18446744073709551615 : BitVec 64) <<< (30 : BitVec 6).toNat)) = (18446744072635809792 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_3_7_1
example (s : riscv_state) : «dfn'SLLI» (1,1,30) (fixture s 3 18446744073709551615) =
 (let t := fixture s 3 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744072635809792 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) <<< (30 : BitVec 6).toNat), 1) (fixture s 3 18446744073709551615) = _
  have numeric : (((18446744073709551615 : BitVec 64) <<< (30 : BitVec 6).toNat)) = (18446744072635809792 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_3_7_7
example (s : riscv_state) : «dfn'SLLI» (7,1,30) (fixture s 3 18446744073709551615) =
 (let t := fixture s 3 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744072635809792 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) <<< (30 : BitVec 6).toNat), 7) (fixture s 3 18446744073709551615) = _
  have numeric : (((18446744073709551615 : BitVec 64) <<< (30 : BitVec 6).toNat)) = (18446744072635809792 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_3_8_0
example (s : riscv_state) : «dfn'SLLI» (0,0,31) (fixture s 3 17) =
 (let t := fixture s 3 17; t) := by
  change «write'GPR» (((0 : BitVec 64) <<< (31 : BitVec 6).toNat), 0) (fixture s 3 17) = _
  have numeric : (((0 : BitVec 64) <<< (31 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_3_8_1
example (s : riscv_state) : «dfn'SLLI» (1,0,31) (fixture s 3 17) =
 (let t := fixture s 3 17; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((0 : BitVec 64) <<< (31 : BitVec 6).toNat), 1) (fixture s 3 17) = _
  have numeric : (((0 : BitVec 64) <<< (31 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_3_8_7
example (s : riscv_state) : «dfn'SLLI» (7,0,31) (fixture s 3 17) =
 (let t := fixture s 3 17; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((0 : BitVec 64) <<< (31 : BitVec 6).toNat), 7) (fixture s 3 17) = _
  have numeric : (((0 : BitVec 64) <<< (31 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_3_9_0
example (s : riscv_state) : «dfn'SLLI» (0,0,1) (fixture s 3 18446744073709551615) =
 (let t := fixture s 3 18446744073709551615; t) := by
  change «write'GPR» (((0 : BitVec 64) <<< (1 : BitVec 6).toNat), 0) (fixture s 3 18446744073709551615) = _
  have numeric : (((0 : BitVec 64) <<< (1 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_3_9_1
example (s : riscv_state) : «dfn'SLLI» (1,0,1) (fixture s 3 18446744073709551615) =
 (let t := fixture s 3 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((0 : BitVec 64) <<< (1 : BitVec 6).toNat), 1) (fixture s 3 18446744073709551615) = _
  have numeric : (((0 : BitVec 64) <<< (1 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SLLI_3_9_7
example (s : riscv_state) : «dfn'SLLI» (7,0,1) (fixture s 3 18446744073709551615) =
 (let t := fixture s 3 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((0 : BitVec 64) <<< (1 : BitVec 6).toNat), 7) (fixture s 3 18446744073709551615) = _
  have numeric : (((0 : BitVec 64) <<< (1 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_0_0_0
example (s : riscv_state) : «dfn'SRLI» (0,1,0) (fixture s 0 9223372036854775808) =
 (let t := fixture s 0 9223372036854775808; t) := by
  change «write'GPR» (((BitVec.setWidth 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) >>> (0 : BitVec 6).toNat), 0) (fixture s 0 9223372036854775808) = _
  have numeric : (((BitVec.setWidth 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) >>> (0 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_0_0_1
example (s : riscv_state) : «dfn'SRLI» (1,1,0) (fixture s 0 9223372036854775808) =
 (let t := fixture s 0 9223372036854775808; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((BitVec.setWidth 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) >>> (0 : BitVec 6).toNat), 1) (fixture s 0 9223372036854775808) = _
  have numeric : (((BitVec.setWidth 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) >>> (0 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_0_0_7
example (s : riscv_state) : «dfn'SRLI» (7,1,0) (fixture s 0 9223372036854775808) =
 (let t := fixture s 0 9223372036854775808; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((BitVec.setWidth 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) >>> (0 : BitVec 6).toNat), 7) (fixture s 0 9223372036854775808) = _
  have numeric : (((BitVec.setWidth 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) >>> (0 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_0_1_0
example (s : riscv_state) : «dfn'SRLI» (0,1,1) (fixture s 0 2147483649) =
 (let t := fixture s 0 2147483649; t) := by
  change «write'GPR» (((BitVec.setWidth 64 (holWordExtract 32 31 0 (2147483649 : BitVec 64))) >>> (1 : BitVec 6).toNat), 0) (fixture s 0 2147483649) = _
  have numeric : (((BitVec.setWidth 64 (holWordExtract 32 31 0 (2147483649 : BitVec 64))) >>> (1 : BitVec 6).toNat)) = (1073741824 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_0_1_1
example (s : riscv_state) : «dfn'SRLI» (1,1,1) (fixture s 0 2147483649) =
 (let t := fixture s 0 2147483649; {t with c_gpr := holUpdate 7 (holUpdate 1 1073741824 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((BitVec.setWidth 64 (holWordExtract 32 31 0 (2147483649 : BitVec 64))) >>> (1 : BitVec 6).toNat), 1) (fixture s 0 2147483649) = _
  have numeric : (((BitVec.setWidth 64 (holWordExtract 32 31 0 (2147483649 : BitVec 64))) >>> (1 : BitVec 6).toNat)) = (1073741824 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_0_1_7
example (s : riscv_state) : «dfn'SRLI» (7,1,1) (fixture s 0 2147483649) =
 (let t := fixture s 0 2147483649; {t with c_gpr := holUpdate 7 (holUpdate 7 1073741824 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((BitVec.setWidth 64 (holWordExtract 32 31 0 (2147483649 : BitVec 64))) >>> (1 : BitVec 6).toNat), 7) (fixture s 0 2147483649) = _
  have numeric : (((BitVec.setWidth 64 (holWordExtract 32 31 0 (2147483649 : BitVec 64))) >>> (1 : BitVec 6).toNat)) = (1073741824 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_0_2_0
example (s : riscv_state) : «dfn'SRLI» (0,1,31) (fixture s 0 4294967297) =
 (let t := fixture s 0 4294967297; t) := by
  change «write'GPR» (((BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) >>> (31 : BitVec 6).toNat), 0) (fixture s 0 4294967297) = _
  have numeric : (((BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) >>> (31 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_0_2_1
example (s : riscv_state) : «dfn'SRLI» (1,1,31) (fixture s 0 4294967297) =
 (let t := fixture s 0 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) >>> (31 : BitVec 6).toNat), 1) (fixture s 0 4294967297) = _
  have numeric : (((BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) >>> (31 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_0_2_7
example (s : riscv_state) : «dfn'SRLI» (7,1,31) (fixture s 0 4294967297) =
 (let t := fixture s 0 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) >>> (31 : BitVec 6).toNat), 7) (fixture s 0 4294967297) = _
  have numeric : (((BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) >>> (31 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_0_3_0
example (s : riscv_state) : «dfn'SRLI» (0,1,32) (fixture s 0 18446744073709551615) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615) := by rfl

-- immediate_shift_SRLI_0_3_1
example (s : riscv_state) : «dfn'SRLI» (1,1,32) (fixture s 0 18446744073709551615) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615) := by rfl

-- immediate_shift_SRLI_0_3_7
example (s : riscv_state) : «dfn'SRLI» (7,1,32) (fixture s 0 18446744073709551615) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615) := by rfl

-- immediate_shift_SRLI_0_4_0
example (s : riscv_state) : «dfn'SRLI» (0,1,33) (fixture s 0 2147483648) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483648) := by rfl

-- immediate_shift_SRLI_0_4_1
example (s : riscv_state) : «dfn'SRLI» (1,1,33) (fixture s 0 2147483648) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483648) := by rfl

-- immediate_shift_SRLI_0_4_7
example (s : riscv_state) : «dfn'SRLI» (7,1,33) (fixture s 0 2147483648) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483648) := by rfl

-- immediate_shift_SRLI_0_5_0
example (s : riscv_state) : «dfn'SRLI» (0,1,63) (fixture s 0 4294967296) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967296) := by rfl

-- immediate_shift_SRLI_0_5_1
example (s : riscv_state) : «dfn'SRLI» (1,1,63) (fixture s 0 4294967296) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967296) := by rfl

-- immediate_shift_SRLI_0_5_7
example (s : riscv_state) : «dfn'SRLI» (7,1,63) (fixture s 0 4294967296) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967296) := by rfl

-- immediate_shift_SRLI_0_6_0
example (s : riscv_state) : «dfn'SRLI» (0,1,15) (fixture s 0 9223372036854775809) =
 (let t := fixture s 0 9223372036854775809; t) := by
  change «write'GPR» (((BitVec.setWidth 64 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64))) >>> (15 : BitVec 6).toNat), 0) (fixture s 0 9223372036854775809) = _
  have numeric : (((BitVec.setWidth 64 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64))) >>> (15 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_0_6_1
example (s : riscv_state) : «dfn'SRLI» (1,1,15) (fixture s 0 9223372036854775809) =
 (let t := fixture s 0 9223372036854775809; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((BitVec.setWidth 64 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64))) >>> (15 : BitVec 6).toNat), 1) (fixture s 0 9223372036854775809) = _
  have numeric : (((BitVec.setWidth 64 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64))) >>> (15 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_0_6_7
example (s : riscv_state) : «dfn'SRLI» (7,1,15) (fixture s 0 9223372036854775809) =
 (let t := fixture s 0 9223372036854775809; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((BitVec.setWidth 64 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64))) >>> (15 : BitVec 6).toNat), 7) (fixture s 0 9223372036854775809) = _
  have numeric : (((BitVec.setWidth 64 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64))) >>> (15 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_0_7_0
example (s : riscv_state) : «dfn'SRLI» (0,1,30) (fixture s 0 18446744073709551615) =
 (let t := fixture s 0 18446744073709551615; t) := by
  change «write'GPR» (((BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) >>> (30 : BitVec 6).toNat), 0) (fixture s 0 18446744073709551615) = _
  have numeric : (((BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) >>> (30 : BitVec 6).toNat)) = (3 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_0_7_1
example (s : riscv_state) : «dfn'SRLI» (1,1,30) (fixture s 0 18446744073709551615) =
 (let t := fixture s 0 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 3 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) >>> (30 : BitVec 6).toNat), 1) (fixture s 0 18446744073709551615) = _
  have numeric : (((BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) >>> (30 : BitVec 6).toNat)) = (3 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_0_7_7
example (s : riscv_state) : «dfn'SRLI» (7,1,30) (fixture s 0 18446744073709551615) =
 (let t := fixture s 0 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 3 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) >>> (30 : BitVec 6).toNat), 7) (fixture s 0 18446744073709551615) = _
  have numeric : (((BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) >>> (30 : BitVec 6).toNat)) = (3 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_0_8_0
example (s : riscv_state) : «dfn'SRLI» (0,0,31) (fixture s 0 17) =
 (let t := fixture s 0 17; t) := by
  change «write'GPR» (((BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) >>> (31 : BitVec 6).toNat), 0) (fixture s 0 17) = _
  have numeric : (((BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) >>> (31 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_0_8_1
example (s : riscv_state) : «dfn'SRLI» (1,0,31) (fixture s 0 17) =
 (let t := fixture s 0 17; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) >>> (31 : BitVec 6).toNat), 1) (fixture s 0 17) = _
  have numeric : (((BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) >>> (31 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_0_8_7
example (s : riscv_state) : «dfn'SRLI» (7,0,31) (fixture s 0 17) =
 (let t := fixture s 0 17; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) >>> (31 : BitVec 6).toNat), 7) (fixture s 0 17) = _
  have numeric : (((BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) >>> (31 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_0_9_0
example (s : riscv_state) : «dfn'SRLI» (0,0,1) (fixture s 0 18446744073709551615) =
 (let t := fixture s 0 18446744073709551615; t) := by
  change «write'GPR» (((BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) >>> (1 : BitVec 6).toNat), 0) (fixture s 0 18446744073709551615) = _
  have numeric : (((BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) >>> (1 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_0_9_1
example (s : riscv_state) : «dfn'SRLI» (1,0,1) (fixture s 0 18446744073709551615) =
 (let t := fixture s 0 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) >>> (1 : BitVec 6).toNat), 1) (fixture s 0 18446744073709551615) = _
  have numeric : (((BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) >>> (1 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_0_9_7
example (s : riscv_state) : «dfn'SRLI» (7,0,1) (fixture s 0 18446744073709551615) =
 (let t := fixture s 0 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) >>> (1 : BitVec 6).toNat), 7) (fixture s 0 18446744073709551615) = _
  have numeric : (((BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) >>> (1 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_2_0_0
example (s : riscv_state) : «dfn'SRLI» (0,1,0) (fixture s 2 9223372036854775808) =
 (let t := fixture s 2 9223372036854775808; t) := by
  change «write'GPR» (((9223372036854775808 : BitVec 64) >>> (0 : BitVec 6).toNat), 0) (fixture s 2 9223372036854775808) = _
  have numeric : (((9223372036854775808 : BitVec 64) >>> (0 : BitVec 6).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_2_0_1
example (s : riscv_state) : «dfn'SRLI» (1,1,0) (fixture s 2 9223372036854775808) =
 (let t := fixture s 2 9223372036854775808; {t with c_gpr := holUpdate 7 (holUpdate 1 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775808 : BitVec 64) >>> (0 : BitVec 6).toNat), 1) (fixture s 2 9223372036854775808) = _
  have numeric : (((9223372036854775808 : BitVec 64) >>> (0 : BitVec 6).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_2_0_7
example (s : riscv_state) : «dfn'SRLI» (7,1,0) (fixture s 2 9223372036854775808) =
 (let t := fixture s 2 9223372036854775808; {t with c_gpr := holUpdate 7 (holUpdate 7 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775808 : BitVec 64) >>> (0 : BitVec 6).toNat), 7) (fixture s 2 9223372036854775808) = _
  have numeric : (((9223372036854775808 : BitVec 64) >>> (0 : BitVec 6).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_2_1_0
example (s : riscv_state) : «dfn'SRLI» (0,1,1) (fixture s 2 2147483649) =
 (let t := fixture s 2 2147483649; t) := by
  change «write'GPR» (((2147483649 : BitVec 64) >>> (1 : BitVec 6).toNat), 0) (fixture s 2 2147483649) = _
  have numeric : (((2147483649 : BitVec 64) >>> (1 : BitVec 6).toNat)) = (1073741824 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_2_1_1
example (s : riscv_state) : «dfn'SRLI» (1,1,1) (fixture s 2 2147483649) =
 (let t := fixture s 2 2147483649; {t with c_gpr := holUpdate 7 (holUpdate 1 1073741824 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((2147483649 : BitVec 64) >>> (1 : BitVec 6).toNat), 1) (fixture s 2 2147483649) = _
  have numeric : (((2147483649 : BitVec 64) >>> (1 : BitVec 6).toNat)) = (1073741824 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_2_1_7
example (s : riscv_state) : «dfn'SRLI» (7,1,1) (fixture s 2 2147483649) =
 (let t := fixture s 2 2147483649; {t with c_gpr := holUpdate 7 (holUpdate 7 1073741824 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((2147483649 : BitVec 64) >>> (1 : BitVec 6).toNat), 7) (fixture s 2 2147483649) = _
  have numeric : (((2147483649 : BitVec 64) >>> (1 : BitVec 6).toNat)) = (1073741824 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_2_2_0
example (s : riscv_state) : «dfn'SRLI» (0,1,31) (fixture s 2 4294967297) =
 (let t := fixture s 2 4294967297; t) := by
  change «write'GPR» (((4294967297 : BitVec 64) >>> (31 : BitVec 6).toNat), 0) (fixture s 2 4294967297) = _
  have numeric : (((4294967297 : BitVec 64) >>> (31 : BitVec 6).toNat)) = (2 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_2_2_1
example (s : riscv_state) : «dfn'SRLI» (1,1,31) (fixture s 2 4294967297) =
 (let t := fixture s 2 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 1 2 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((4294967297 : BitVec 64) >>> (31 : BitVec 6).toNat), 1) (fixture s 2 4294967297) = _
  have numeric : (((4294967297 : BitVec 64) >>> (31 : BitVec 6).toNat)) = (2 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_2_2_7
example (s : riscv_state) : «dfn'SRLI» (7,1,31) (fixture s 2 4294967297) =
 (let t := fixture s 2 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 7 2 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((4294967297 : BitVec 64) >>> (31 : BitVec 6).toNat), 7) (fixture s 2 4294967297) = _
  have numeric : (((4294967297 : BitVec 64) >>> (31 : BitVec 6).toNat)) = (2 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_2_3_0
example (s : riscv_state) : «dfn'SRLI» (0,1,32) (fixture s 2 18446744073709551615) =
 (let t := fixture s 2 18446744073709551615; t) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) >>> (32 : BitVec 6).toNat), 0) (fixture s 2 18446744073709551615) = _
  have numeric : (((18446744073709551615 : BitVec 64) >>> (32 : BitVec 6).toNat)) = (4294967295 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_2_3_1
example (s : riscv_state) : «dfn'SRLI» (1,1,32) (fixture s 2 18446744073709551615) =
 (let t := fixture s 2 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 4294967295 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) >>> (32 : BitVec 6).toNat), 1) (fixture s 2 18446744073709551615) = _
  have numeric : (((18446744073709551615 : BitVec 64) >>> (32 : BitVec 6).toNat)) = (4294967295 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_2_3_7
example (s : riscv_state) : «dfn'SRLI» (7,1,32) (fixture s 2 18446744073709551615) =
 (let t := fixture s 2 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 4294967295 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) >>> (32 : BitVec 6).toNat), 7) (fixture s 2 18446744073709551615) = _
  have numeric : (((18446744073709551615 : BitVec 64) >>> (32 : BitVec 6).toNat)) = (4294967295 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_2_4_0
example (s : riscv_state) : «dfn'SRLI» (0,1,33) (fixture s 2 2147483648) =
 (let t := fixture s 2 2147483648; t) := by
  change «write'GPR» (((2147483648 : BitVec 64) >>> (33 : BitVec 6).toNat), 0) (fixture s 2 2147483648) = _
  have numeric : (((2147483648 : BitVec 64) >>> (33 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_2_4_1
example (s : riscv_state) : «dfn'SRLI» (1,1,33) (fixture s 2 2147483648) =
 (let t := fixture s 2 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((2147483648 : BitVec 64) >>> (33 : BitVec 6).toNat), 1) (fixture s 2 2147483648) = _
  have numeric : (((2147483648 : BitVec 64) >>> (33 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_2_4_7
example (s : riscv_state) : «dfn'SRLI» (7,1,33) (fixture s 2 2147483648) =
 (let t := fixture s 2 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((2147483648 : BitVec 64) >>> (33 : BitVec 6).toNat), 7) (fixture s 2 2147483648) = _
  have numeric : (((2147483648 : BitVec 64) >>> (33 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_2_5_0
example (s : riscv_state) : «dfn'SRLI» (0,1,63) (fixture s 2 4294967296) =
 (let t := fixture s 2 4294967296; t) := by
  change «write'GPR» (((4294967296 : BitVec 64) >>> (63 : BitVec 6).toNat), 0) (fixture s 2 4294967296) = _
  have numeric : (((4294967296 : BitVec 64) >>> (63 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_2_5_1
example (s : riscv_state) : «dfn'SRLI» (1,1,63) (fixture s 2 4294967296) =
 (let t := fixture s 2 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((4294967296 : BitVec 64) >>> (63 : BitVec 6).toNat), 1) (fixture s 2 4294967296) = _
  have numeric : (((4294967296 : BitVec 64) >>> (63 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_2_5_7
example (s : riscv_state) : «dfn'SRLI» (7,1,63) (fixture s 2 4294967296) =
 (let t := fixture s 2 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((4294967296 : BitVec 64) >>> (63 : BitVec 6).toNat), 7) (fixture s 2 4294967296) = _
  have numeric : (((4294967296 : BitVec 64) >>> (63 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_2_6_0
example (s : riscv_state) : «dfn'SRLI» (0,1,15) (fixture s 2 9223372036854775809) =
 (let t := fixture s 2 9223372036854775809; t) := by
  change «write'GPR» (((9223372036854775809 : BitVec 64) >>> (15 : BitVec 6).toNat), 0) (fixture s 2 9223372036854775809) = _
  have numeric : (((9223372036854775809 : BitVec 64) >>> (15 : BitVec 6).toNat)) = (281474976710656 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_2_6_1
example (s : riscv_state) : «dfn'SRLI» (1,1,15) (fixture s 2 9223372036854775809) =
 (let t := fixture s 2 9223372036854775809; {t with c_gpr := holUpdate 7 (holUpdate 1 281474976710656 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775809 : BitVec 64) >>> (15 : BitVec 6).toNat), 1) (fixture s 2 9223372036854775809) = _
  have numeric : (((9223372036854775809 : BitVec 64) >>> (15 : BitVec 6).toNat)) = (281474976710656 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_2_6_7
example (s : riscv_state) : «dfn'SRLI» (7,1,15) (fixture s 2 9223372036854775809) =
 (let t := fixture s 2 9223372036854775809; {t with c_gpr := holUpdate 7 (holUpdate 7 281474976710656 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775809 : BitVec 64) >>> (15 : BitVec 6).toNat), 7) (fixture s 2 9223372036854775809) = _
  have numeric : (((9223372036854775809 : BitVec 64) >>> (15 : BitVec 6).toNat)) = (281474976710656 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_2_7_0
example (s : riscv_state) : «dfn'SRLI» (0,1,30) (fixture s 2 18446744073709551615) =
 (let t := fixture s 2 18446744073709551615; t) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) >>> (30 : BitVec 6).toNat), 0) (fixture s 2 18446744073709551615) = _
  have numeric : (((18446744073709551615 : BitVec 64) >>> (30 : BitVec 6).toNat)) = (17179869183 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_2_7_1
example (s : riscv_state) : «dfn'SRLI» (1,1,30) (fixture s 2 18446744073709551615) =
 (let t := fixture s 2 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 17179869183 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) >>> (30 : BitVec 6).toNat), 1) (fixture s 2 18446744073709551615) = _
  have numeric : (((18446744073709551615 : BitVec 64) >>> (30 : BitVec 6).toNat)) = (17179869183 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_2_7_7
example (s : riscv_state) : «dfn'SRLI» (7,1,30) (fixture s 2 18446744073709551615) =
 (let t := fixture s 2 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 17179869183 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) >>> (30 : BitVec 6).toNat), 7) (fixture s 2 18446744073709551615) = _
  have numeric : (((18446744073709551615 : BitVec 64) >>> (30 : BitVec 6).toNat)) = (17179869183 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_2_8_0
example (s : riscv_state) : «dfn'SRLI» (0,0,31) (fixture s 2 17) =
 (let t := fixture s 2 17; t) := by
  change «write'GPR» (((0 : BitVec 64) >>> (31 : BitVec 6).toNat), 0) (fixture s 2 17) = _
  have numeric : (((0 : BitVec 64) >>> (31 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_2_8_1
example (s : riscv_state) : «dfn'SRLI» (1,0,31) (fixture s 2 17) =
 (let t := fixture s 2 17; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((0 : BitVec 64) >>> (31 : BitVec 6).toNat), 1) (fixture s 2 17) = _
  have numeric : (((0 : BitVec 64) >>> (31 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_2_8_7
example (s : riscv_state) : «dfn'SRLI» (7,0,31) (fixture s 2 17) =
 (let t := fixture s 2 17; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((0 : BitVec 64) >>> (31 : BitVec 6).toNat), 7) (fixture s 2 17) = _
  have numeric : (((0 : BitVec 64) >>> (31 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_2_9_0
example (s : riscv_state) : «dfn'SRLI» (0,0,1) (fixture s 2 18446744073709551615) =
 (let t := fixture s 2 18446744073709551615; t) := by
  change «write'GPR» (((0 : BitVec 64) >>> (1 : BitVec 6).toNat), 0) (fixture s 2 18446744073709551615) = _
  have numeric : (((0 : BitVec 64) >>> (1 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_2_9_1
example (s : riscv_state) : «dfn'SRLI» (1,0,1) (fixture s 2 18446744073709551615) =
 (let t := fixture s 2 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((0 : BitVec 64) >>> (1 : BitVec 6).toNat), 1) (fixture s 2 18446744073709551615) = _
  have numeric : (((0 : BitVec 64) >>> (1 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_2_9_7
example (s : riscv_state) : «dfn'SRLI» (7,0,1) (fixture s 2 18446744073709551615) =
 (let t := fixture s 2 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((0 : BitVec 64) >>> (1 : BitVec 6).toNat), 7) (fixture s 2 18446744073709551615) = _
  have numeric : (((0 : BitVec 64) >>> (1 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_3_0_0
example (s : riscv_state) : «dfn'SRLI» (0,1,0) (fixture s 3 9223372036854775808) =
 (let t := fixture s 3 9223372036854775808; t) := by
  change «write'GPR» (((9223372036854775808 : BitVec 64) >>> (0 : BitVec 6).toNat), 0) (fixture s 3 9223372036854775808) = _
  have numeric : (((9223372036854775808 : BitVec 64) >>> (0 : BitVec 6).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_3_0_1
example (s : riscv_state) : «dfn'SRLI» (1,1,0) (fixture s 3 9223372036854775808) =
 (let t := fixture s 3 9223372036854775808; {t with c_gpr := holUpdate 7 (holUpdate 1 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775808 : BitVec 64) >>> (0 : BitVec 6).toNat), 1) (fixture s 3 9223372036854775808) = _
  have numeric : (((9223372036854775808 : BitVec 64) >>> (0 : BitVec 6).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_3_0_7
example (s : riscv_state) : «dfn'SRLI» (7,1,0) (fixture s 3 9223372036854775808) =
 (let t := fixture s 3 9223372036854775808; {t with c_gpr := holUpdate 7 (holUpdate 7 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775808 : BitVec 64) >>> (0 : BitVec 6).toNat), 7) (fixture s 3 9223372036854775808) = _
  have numeric : (((9223372036854775808 : BitVec 64) >>> (0 : BitVec 6).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_3_1_0
example (s : riscv_state) : «dfn'SRLI» (0,1,1) (fixture s 3 2147483649) =
 (let t := fixture s 3 2147483649; t) := by
  change «write'GPR» (((2147483649 : BitVec 64) >>> (1 : BitVec 6).toNat), 0) (fixture s 3 2147483649) = _
  have numeric : (((2147483649 : BitVec 64) >>> (1 : BitVec 6).toNat)) = (1073741824 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_3_1_1
example (s : riscv_state) : «dfn'SRLI» (1,1,1) (fixture s 3 2147483649) =
 (let t := fixture s 3 2147483649; {t with c_gpr := holUpdate 7 (holUpdate 1 1073741824 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((2147483649 : BitVec 64) >>> (1 : BitVec 6).toNat), 1) (fixture s 3 2147483649) = _
  have numeric : (((2147483649 : BitVec 64) >>> (1 : BitVec 6).toNat)) = (1073741824 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_3_1_7
example (s : riscv_state) : «dfn'SRLI» (7,1,1) (fixture s 3 2147483649) =
 (let t := fixture s 3 2147483649; {t with c_gpr := holUpdate 7 (holUpdate 7 1073741824 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((2147483649 : BitVec 64) >>> (1 : BitVec 6).toNat), 7) (fixture s 3 2147483649) = _
  have numeric : (((2147483649 : BitVec 64) >>> (1 : BitVec 6).toNat)) = (1073741824 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_3_2_0
example (s : riscv_state) : «dfn'SRLI» (0,1,31) (fixture s 3 4294967297) =
 (let t := fixture s 3 4294967297; t) := by
  change «write'GPR» (((4294967297 : BitVec 64) >>> (31 : BitVec 6).toNat), 0) (fixture s 3 4294967297) = _
  have numeric : (((4294967297 : BitVec 64) >>> (31 : BitVec 6).toNat)) = (2 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_3_2_1
example (s : riscv_state) : «dfn'SRLI» (1,1,31) (fixture s 3 4294967297) =
 (let t := fixture s 3 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 1 2 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((4294967297 : BitVec 64) >>> (31 : BitVec 6).toNat), 1) (fixture s 3 4294967297) = _
  have numeric : (((4294967297 : BitVec 64) >>> (31 : BitVec 6).toNat)) = (2 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_3_2_7
example (s : riscv_state) : «dfn'SRLI» (7,1,31) (fixture s 3 4294967297) =
 (let t := fixture s 3 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 7 2 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((4294967297 : BitVec 64) >>> (31 : BitVec 6).toNat), 7) (fixture s 3 4294967297) = _
  have numeric : (((4294967297 : BitVec 64) >>> (31 : BitVec 6).toNat)) = (2 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_3_3_0
example (s : riscv_state) : «dfn'SRLI» (0,1,32) (fixture s 3 18446744073709551615) =
 (let t := fixture s 3 18446744073709551615; t) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) >>> (32 : BitVec 6).toNat), 0) (fixture s 3 18446744073709551615) = _
  have numeric : (((18446744073709551615 : BitVec 64) >>> (32 : BitVec 6).toNat)) = (4294967295 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_3_3_1
example (s : riscv_state) : «dfn'SRLI» (1,1,32) (fixture s 3 18446744073709551615) =
 (let t := fixture s 3 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 4294967295 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) >>> (32 : BitVec 6).toNat), 1) (fixture s 3 18446744073709551615) = _
  have numeric : (((18446744073709551615 : BitVec 64) >>> (32 : BitVec 6).toNat)) = (4294967295 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_3_3_7
example (s : riscv_state) : «dfn'SRLI» (7,1,32) (fixture s 3 18446744073709551615) =
 (let t := fixture s 3 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 4294967295 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) >>> (32 : BitVec 6).toNat), 7) (fixture s 3 18446744073709551615) = _
  have numeric : (((18446744073709551615 : BitVec 64) >>> (32 : BitVec 6).toNat)) = (4294967295 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_3_4_0
example (s : riscv_state) : «dfn'SRLI» (0,1,33) (fixture s 3 2147483648) =
 (let t := fixture s 3 2147483648; t) := by
  change «write'GPR» (((2147483648 : BitVec 64) >>> (33 : BitVec 6).toNat), 0) (fixture s 3 2147483648) = _
  have numeric : (((2147483648 : BitVec 64) >>> (33 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_3_4_1
example (s : riscv_state) : «dfn'SRLI» (1,1,33) (fixture s 3 2147483648) =
 (let t := fixture s 3 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((2147483648 : BitVec 64) >>> (33 : BitVec 6).toNat), 1) (fixture s 3 2147483648) = _
  have numeric : (((2147483648 : BitVec 64) >>> (33 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_3_4_7
example (s : riscv_state) : «dfn'SRLI» (7,1,33) (fixture s 3 2147483648) =
 (let t := fixture s 3 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((2147483648 : BitVec 64) >>> (33 : BitVec 6).toNat), 7) (fixture s 3 2147483648) = _
  have numeric : (((2147483648 : BitVec 64) >>> (33 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_3_5_0
example (s : riscv_state) : «dfn'SRLI» (0,1,63) (fixture s 3 4294967296) =
 (let t := fixture s 3 4294967296; t) := by
  change «write'GPR» (((4294967296 : BitVec 64) >>> (63 : BitVec 6).toNat), 0) (fixture s 3 4294967296) = _
  have numeric : (((4294967296 : BitVec 64) >>> (63 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_3_5_1
example (s : riscv_state) : «dfn'SRLI» (1,1,63) (fixture s 3 4294967296) =
 (let t := fixture s 3 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((4294967296 : BitVec 64) >>> (63 : BitVec 6).toNat), 1) (fixture s 3 4294967296) = _
  have numeric : (((4294967296 : BitVec 64) >>> (63 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_3_5_7
example (s : riscv_state) : «dfn'SRLI» (7,1,63) (fixture s 3 4294967296) =
 (let t := fixture s 3 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((4294967296 : BitVec 64) >>> (63 : BitVec 6).toNat), 7) (fixture s 3 4294967296) = _
  have numeric : (((4294967296 : BitVec 64) >>> (63 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_3_6_0
example (s : riscv_state) : «dfn'SRLI» (0,1,15) (fixture s 3 9223372036854775809) =
 (let t := fixture s 3 9223372036854775809; t) := by
  change «write'GPR» (((9223372036854775809 : BitVec 64) >>> (15 : BitVec 6).toNat), 0) (fixture s 3 9223372036854775809) = _
  have numeric : (((9223372036854775809 : BitVec 64) >>> (15 : BitVec 6).toNat)) = (281474976710656 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_3_6_1
example (s : riscv_state) : «dfn'SRLI» (1,1,15) (fixture s 3 9223372036854775809) =
 (let t := fixture s 3 9223372036854775809; {t with c_gpr := holUpdate 7 (holUpdate 1 281474976710656 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775809 : BitVec 64) >>> (15 : BitVec 6).toNat), 1) (fixture s 3 9223372036854775809) = _
  have numeric : (((9223372036854775809 : BitVec 64) >>> (15 : BitVec 6).toNat)) = (281474976710656 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_3_6_7
example (s : riscv_state) : «dfn'SRLI» (7,1,15) (fixture s 3 9223372036854775809) =
 (let t := fixture s 3 9223372036854775809; {t with c_gpr := holUpdate 7 (holUpdate 7 281474976710656 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775809 : BitVec 64) >>> (15 : BitVec 6).toNat), 7) (fixture s 3 9223372036854775809) = _
  have numeric : (((9223372036854775809 : BitVec 64) >>> (15 : BitVec 6).toNat)) = (281474976710656 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_3_7_0
example (s : riscv_state) : «dfn'SRLI» (0,1,30) (fixture s 3 18446744073709551615) =
 (let t := fixture s 3 18446744073709551615; t) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) >>> (30 : BitVec 6).toNat), 0) (fixture s 3 18446744073709551615) = _
  have numeric : (((18446744073709551615 : BitVec 64) >>> (30 : BitVec 6).toNat)) = (17179869183 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_3_7_1
example (s : riscv_state) : «dfn'SRLI» (1,1,30) (fixture s 3 18446744073709551615) =
 (let t := fixture s 3 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 17179869183 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) >>> (30 : BitVec 6).toNat), 1) (fixture s 3 18446744073709551615) = _
  have numeric : (((18446744073709551615 : BitVec 64) >>> (30 : BitVec 6).toNat)) = (17179869183 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_3_7_7
example (s : riscv_state) : «dfn'SRLI» (7,1,30) (fixture s 3 18446744073709551615) =
 (let t := fixture s 3 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 17179869183 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) >>> (30 : BitVec 6).toNat), 7) (fixture s 3 18446744073709551615) = _
  have numeric : (((18446744073709551615 : BitVec 64) >>> (30 : BitVec 6).toNat)) = (17179869183 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_3_8_0
example (s : riscv_state) : «dfn'SRLI» (0,0,31) (fixture s 3 17) =
 (let t := fixture s 3 17; t) := by
  change «write'GPR» (((0 : BitVec 64) >>> (31 : BitVec 6).toNat), 0) (fixture s 3 17) = _
  have numeric : (((0 : BitVec 64) >>> (31 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_3_8_1
example (s : riscv_state) : «dfn'SRLI» (1,0,31) (fixture s 3 17) =
 (let t := fixture s 3 17; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((0 : BitVec 64) >>> (31 : BitVec 6).toNat), 1) (fixture s 3 17) = _
  have numeric : (((0 : BitVec 64) >>> (31 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_3_8_7
example (s : riscv_state) : «dfn'SRLI» (7,0,31) (fixture s 3 17) =
 (let t := fixture s 3 17; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((0 : BitVec 64) >>> (31 : BitVec 6).toNat), 7) (fixture s 3 17) = _
  have numeric : (((0 : BitVec 64) >>> (31 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_3_9_0
example (s : riscv_state) : «dfn'SRLI» (0,0,1) (fixture s 3 18446744073709551615) =
 (let t := fixture s 3 18446744073709551615; t) := by
  change «write'GPR» (((0 : BitVec 64) >>> (1 : BitVec 6).toNat), 0) (fixture s 3 18446744073709551615) = _
  have numeric : (((0 : BitVec 64) >>> (1 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_3_9_1
example (s : riscv_state) : «dfn'SRLI» (1,0,1) (fixture s 3 18446744073709551615) =
 (let t := fixture s 3 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((0 : BitVec 64) >>> (1 : BitVec 6).toNat), 1) (fixture s 3 18446744073709551615) = _
  have numeric : (((0 : BitVec 64) >>> (1 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRLI_3_9_7
example (s : riscv_state) : «dfn'SRLI» (7,0,1) (fixture s 3 18446744073709551615) =
 (let t := fixture s 3 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((0 : BitVec 64) >>> (1 : BitVec 6).toNat), 7) (fixture s 3 18446744073709551615) = _
  have numeric : (((0 : BitVec 64) >>> (1 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_0_0_0
example (s : riscv_state) : «dfn'SRAI» (0,1,0) (fixture s 0 9223372036854775808) =
 (let t := fixture s 0 9223372036854775808; t) := by
  change «write'GPR» ((BitVec.sshiftRight (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (0 : BitVec 6).toNat), 0) (fixture s 0 9223372036854775808) = _
  have numeric : ((BitVec.sshiftRight (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (0 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_0_0_1
example (s : riscv_state) : «dfn'SRAI» (1,1,0) (fixture s 0 9223372036854775808) =
 (let t := fixture s 0 9223372036854775808; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (0 : BitVec 6).toNat), 1) (fixture s 0 9223372036854775808) = _
  have numeric : ((BitVec.sshiftRight (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (0 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_0_0_7
example (s : riscv_state) : «dfn'SRAI» (7,1,0) (fixture s 0 9223372036854775808) =
 (let t := fixture s 0 9223372036854775808; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (0 : BitVec 6).toNat), 7) (fixture s 0 9223372036854775808) = _
  have numeric : ((BitVec.sshiftRight (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (0 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_0_1_0
example (s : riscv_state) : «dfn'SRAI» (0,1,1) (fixture s 0 2147483649) =
 (let t := fixture s 0 2147483649; t) := by
  change «write'GPR» ((BitVec.sshiftRight (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483649 : BitVec 64))) (1 : BitVec 6).toNat), 0) (fixture s 0 2147483649) = _
  have numeric : ((BitVec.sshiftRight (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483649 : BitVec 64))) (1 : BitVec 6).toNat)) = (18446744072635809792 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_0_1_1
example (s : riscv_state) : «dfn'SRAI» (1,1,1) (fixture s 0 2147483649) =
 (let t := fixture s 0 2147483649; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744072635809792 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483649 : BitVec 64))) (1 : BitVec 6).toNat), 1) (fixture s 0 2147483649) = _
  have numeric : ((BitVec.sshiftRight (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483649 : BitVec 64))) (1 : BitVec 6).toNat)) = (18446744072635809792 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_0_1_7
example (s : riscv_state) : «dfn'SRAI» (7,1,1) (fixture s 0 2147483649) =
 (let t := fixture s 0 2147483649; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744072635809792 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483649 : BitVec 64))) (1 : BitVec 6).toNat), 7) (fixture s 0 2147483649) = _
  have numeric : ((BitVec.sshiftRight (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483649 : BitVec 64))) (1 : BitVec 6).toNat)) = (18446744072635809792 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_0_2_0
example (s : riscv_state) : «dfn'SRAI» (0,1,31) (fixture s 0 4294967297) =
 (let t := fixture s 0 4294967297; t) := by
  change «write'GPR» ((BitVec.sshiftRight (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) (31 : BitVec 6).toNat), 0) (fixture s 0 4294967297) = _
  have numeric : ((BitVec.sshiftRight (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) (31 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_0_2_1
example (s : riscv_state) : «dfn'SRAI» (1,1,31) (fixture s 0 4294967297) =
 (let t := fixture s 0 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) (31 : BitVec 6).toNat), 1) (fixture s 0 4294967297) = _
  have numeric : ((BitVec.sshiftRight (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) (31 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_0_2_7
example (s : riscv_state) : «dfn'SRAI» (7,1,31) (fixture s 0 4294967297) =
 (let t := fixture s 0 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) (31 : BitVec 6).toNat), 7) (fixture s 0 4294967297) = _
  have numeric : ((BitVec.sshiftRight (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) (31 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_0_3_0
example (s : riscv_state) : «dfn'SRAI» (0,1,32) (fixture s 0 18446744073709551615) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615) := by rfl

-- immediate_shift_SRAI_0_3_1
example (s : riscv_state) : «dfn'SRAI» (1,1,32) (fixture s 0 18446744073709551615) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615) := by rfl

-- immediate_shift_SRAI_0_3_7
example (s : riscv_state) : «dfn'SRAI» (7,1,32) (fixture s 0 18446744073709551615) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615) := by rfl

-- immediate_shift_SRAI_0_4_0
example (s : riscv_state) : «dfn'SRAI» (0,1,33) (fixture s 0 2147483648) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483648) := by rfl

-- immediate_shift_SRAI_0_4_1
example (s : riscv_state) : «dfn'SRAI» (1,1,33) (fixture s 0 2147483648) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483648) := by rfl

-- immediate_shift_SRAI_0_4_7
example (s : riscv_state) : «dfn'SRAI» (7,1,33) (fixture s 0 2147483648) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483648) := by rfl

-- immediate_shift_SRAI_0_5_0
example (s : riscv_state) : «dfn'SRAI» (0,1,63) (fixture s 0 4294967296) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967296) := by rfl

-- immediate_shift_SRAI_0_5_1
example (s : riscv_state) : «dfn'SRAI» (1,1,63) (fixture s 0 4294967296) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967296) := by rfl

-- immediate_shift_SRAI_0_5_7
example (s : riscv_state) : «dfn'SRAI» (7,1,63) (fixture s 0 4294967296) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967296) := by rfl

-- immediate_shift_SRAI_0_6_0
example (s : riscv_state) : «dfn'SRAI» (0,1,15) (fixture s 0 9223372036854775809) =
 (let t := fixture s 0 9223372036854775809; t) := by
  change «write'GPR» ((BitVec.sshiftRight (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64))) (15 : BitVec 6).toNat), 0) (fixture s 0 9223372036854775809) = _
  have numeric : ((BitVec.sshiftRight (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64))) (15 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_0_6_1
example (s : riscv_state) : «dfn'SRAI» (1,1,15) (fixture s 0 9223372036854775809) =
 (let t := fixture s 0 9223372036854775809; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64))) (15 : BitVec 6).toNat), 1) (fixture s 0 9223372036854775809) = _
  have numeric : ((BitVec.sshiftRight (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64))) (15 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_0_6_7
example (s : riscv_state) : «dfn'SRAI» (7,1,15) (fixture s 0 9223372036854775809) =
 (let t := fixture s 0 9223372036854775809; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64))) (15 : BitVec 6).toNat), 7) (fixture s 0 9223372036854775809) = _
  have numeric : ((BitVec.sshiftRight (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64))) (15 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_0_7_0
example (s : riscv_state) : «dfn'SRAI» (0,1,30) (fixture s 0 18446744073709551615) =
 (let t := fixture s 0 18446744073709551615; t) := by
  change «write'GPR» ((BitVec.sshiftRight (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (30 : BitVec 6).toNat), 0) (fixture s 0 18446744073709551615) = _
  have numeric : ((BitVec.sshiftRight (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (30 : BitVec 6).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_0_7_1
example (s : riscv_state) : «dfn'SRAI» (1,1,30) (fixture s 0 18446744073709551615) =
 (let t := fixture s 0 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (30 : BitVec 6).toNat), 1) (fixture s 0 18446744073709551615) = _
  have numeric : ((BitVec.sshiftRight (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (30 : BitVec 6).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_0_7_7
example (s : riscv_state) : «dfn'SRAI» (7,1,30) (fixture s 0 18446744073709551615) =
 (let t := fixture s 0 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (30 : BitVec 6).toNat), 7) (fixture s 0 18446744073709551615) = _
  have numeric : ((BitVec.sshiftRight (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (30 : BitVec 6).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_0_8_0
example (s : riscv_state) : «dfn'SRAI» (0,0,31) (fixture s 0 17) =
 (let t := fixture s 0 17; t) := by
  change «write'GPR» ((BitVec.sshiftRight (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (31 : BitVec 6).toNat), 0) (fixture s 0 17) = _
  have numeric : ((BitVec.sshiftRight (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (31 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_0_8_1
example (s : riscv_state) : «dfn'SRAI» (1,0,31) (fixture s 0 17) =
 (let t := fixture s 0 17; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (31 : BitVec 6).toNat), 1) (fixture s 0 17) = _
  have numeric : ((BitVec.sshiftRight (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (31 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_0_8_7
example (s : riscv_state) : «dfn'SRAI» (7,0,31) (fixture s 0 17) =
 (let t := fixture s 0 17; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (31 : BitVec 6).toNat), 7) (fixture s 0 17) = _
  have numeric : ((BitVec.sshiftRight (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (31 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_0_9_0
example (s : riscv_state) : «dfn'SRAI» (0,0,1) (fixture s 0 18446744073709551615) =
 (let t := fixture s 0 18446744073709551615; t) := by
  change «write'GPR» ((BitVec.sshiftRight (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (1 : BitVec 6).toNat), 0) (fixture s 0 18446744073709551615) = _
  have numeric : ((BitVec.sshiftRight (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (1 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_0_9_1
example (s : riscv_state) : «dfn'SRAI» (1,0,1) (fixture s 0 18446744073709551615) =
 (let t := fixture s 0 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (1 : BitVec 6).toNat), 1) (fixture s 0 18446744073709551615) = _
  have numeric : ((BitVec.sshiftRight (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (1 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_0_9_7
example (s : riscv_state) : «dfn'SRAI» (7,0,1) (fixture s 0 18446744073709551615) =
 (let t := fixture s 0 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (1 : BitVec 6).toNat), 7) (fixture s 0 18446744073709551615) = _
  have numeric : ((BitVec.sshiftRight (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (1 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_2_0_0
example (s : riscv_state) : «dfn'SRAI» (0,1,0) (fixture s 2 9223372036854775808) =
 (let t := fixture s 2 9223372036854775808; t) := by
  change «write'GPR» ((BitVec.sshiftRight (9223372036854775808 : BitVec 64) (0 : BitVec 6).toNat), 0) (fixture s 2 9223372036854775808) = _
  have numeric : ((BitVec.sshiftRight (9223372036854775808 : BitVec 64) (0 : BitVec 6).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_2_0_1
example (s : riscv_state) : «dfn'SRAI» (1,1,0) (fixture s 2 9223372036854775808) =
 (let t := fixture s 2 9223372036854775808; {t with c_gpr := holUpdate 7 (holUpdate 1 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (9223372036854775808 : BitVec 64) (0 : BitVec 6).toNat), 1) (fixture s 2 9223372036854775808) = _
  have numeric : ((BitVec.sshiftRight (9223372036854775808 : BitVec 64) (0 : BitVec 6).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_2_0_7
example (s : riscv_state) : «dfn'SRAI» (7,1,0) (fixture s 2 9223372036854775808) =
 (let t := fixture s 2 9223372036854775808; {t with c_gpr := holUpdate 7 (holUpdate 7 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (9223372036854775808 : BitVec 64) (0 : BitVec 6).toNat), 7) (fixture s 2 9223372036854775808) = _
  have numeric : ((BitVec.sshiftRight (9223372036854775808 : BitVec 64) (0 : BitVec 6).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_2_1_0
example (s : riscv_state) : «dfn'SRAI» (0,1,1) (fixture s 2 2147483649) =
 (let t := fixture s 2 2147483649; t) := by
  change «write'GPR» ((BitVec.sshiftRight (2147483649 : BitVec 64) (1 : BitVec 6).toNat), 0) (fixture s 2 2147483649) = _
  have numeric : ((BitVec.sshiftRight (2147483649 : BitVec 64) (1 : BitVec 6).toNat)) = (1073741824 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_2_1_1
example (s : riscv_state) : «dfn'SRAI» (1,1,1) (fixture s 2 2147483649) =
 (let t := fixture s 2 2147483649; {t with c_gpr := holUpdate 7 (holUpdate 1 1073741824 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (2147483649 : BitVec 64) (1 : BitVec 6).toNat), 1) (fixture s 2 2147483649) = _
  have numeric : ((BitVec.sshiftRight (2147483649 : BitVec 64) (1 : BitVec 6).toNat)) = (1073741824 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_2_1_7
example (s : riscv_state) : «dfn'SRAI» (7,1,1) (fixture s 2 2147483649) =
 (let t := fixture s 2 2147483649; {t with c_gpr := holUpdate 7 (holUpdate 7 1073741824 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (2147483649 : BitVec 64) (1 : BitVec 6).toNat), 7) (fixture s 2 2147483649) = _
  have numeric : ((BitVec.sshiftRight (2147483649 : BitVec 64) (1 : BitVec 6).toNat)) = (1073741824 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_2_2_0
example (s : riscv_state) : «dfn'SRAI» (0,1,31) (fixture s 2 4294967297) =
 (let t := fixture s 2 4294967297; t) := by
  change «write'GPR» ((BitVec.sshiftRight (4294967297 : BitVec 64) (31 : BitVec 6).toNat), 0) (fixture s 2 4294967297) = _
  have numeric : ((BitVec.sshiftRight (4294967297 : BitVec 64) (31 : BitVec 6).toNat)) = (2 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_2_2_1
example (s : riscv_state) : «dfn'SRAI» (1,1,31) (fixture s 2 4294967297) =
 (let t := fixture s 2 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 1 2 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (4294967297 : BitVec 64) (31 : BitVec 6).toNat), 1) (fixture s 2 4294967297) = _
  have numeric : ((BitVec.sshiftRight (4294967297 : BitVec 64) (31 : BitVec 6).toNat)) = (2 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_2_2_7
example (s : riscv_state) : «dfn'SRAI» (7,1,31) (fixture s 2 4294967297) =
 (let t := fixture s 2 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 7 2 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (4294967297 : BitVec 64) (31 : BitVec 6).toNat), 7) (fixture s 2 4294967297) = _
  have numeric : ((BitVec.sshiftRight (4294967297 : BitVec 64) (31 : BitVec 6).toNat)) = (2 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_2_3_0
example (s : riscv_state) : «dfn'SRAI» (0,1,32) (fixture s 2 18446744073709551615) =
 (let t := fixture s 2 18446744073709551615; t) := by
  change «write'GPR» ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (32 : BitVec 6).toNat), 0) (fixture s 2 18446744073709551615) = _
  have numeric : ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (32 : BitVec 6).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_2_3_1
example (s : riscv_state) : «dfn'SRAI» (1,1,32) (fixture s 2 18446744073709551615) =
 (let t := fixture s 2 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (32 : BitVec 6).toNat), 1) (fixture s 2 18446744073709551615) = _
  have numeric : ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (32 : BitVec 6).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_2_3_7
example (s : riscv_state) : «dfn'SRAI» (7,1,32) (fixture s 2 18446744073709551615) =
 (let t := fixture s 2 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (32 : BitVec 6).toNat), 7) (fixture s 2 18446744073709551615) = _
  have numeric : ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (32 : BitVec 6).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_2_4_0
example (s : riscv_state) : «dfn'SRAI» (0,1,33) (fixture s 2 2147483648) =
 (let t := fixture s 2 2147483648; t) := by
  change «write'GPR» ((BitVec.sshiftRight (2147483648 : BitVec 64) (33 : BitVec 6).toNat), 0) (fixture s 2 2147483648) = _
  have numeric : ((BitVec.sshiftRight (2147483648 : BitVec 64) (33 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_2_4_1
example (s : riscv_state) : «dfn'SRAI» (1,1,33) (fixture s 2 2147483648) =
 (let t := fixture s 2 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (2147483648 : BitVec 64) (33 : BitVec 6).toNat), 1) (fixture s 2 2147483648) = _
  have numeric : ((BitVec.sshiftRight (2147483648 : BitVec 64) (33 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_2_4_7
example (s : riscv_state) : «dfn'SRAI» (7,1,33) (fixture s 2 2147483648) =
 (let t := fixture s 2 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (2147483648 : BitVec 64) (33 : BitVec 6).toNat), 7) (fixture s 2 2147483648) = _
  have numeric : ((BitVec.sshiftRight (2147483648 : BitVec 64) (33 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_2_5_0
example (s : riscv_state) : «dfn'SRAI» (0,1,63) (fixture s 2 4294967296) =
 (let t := fixture s 2 4294967296; t) := by
  change «write'GPR» ((BitVec.sshiftRight (4294967296 : BitVec 64) (63 : BitVec 6).toNat), 0) (fixture s 2 4294967296) = _
  have numeric : ((BitVec.sshiftRight (4294967296 : BitVec 64) (63 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_2_5_1
example (s : riscv_state) : «dfn'SRAI» (1,1,63) (fixture s 2 4294967296) =
 (let t := fixture s 2 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (4294967296 : BitVec 64) (63 : BitVec 6).toNat), 1) (fixture s 2 4294967296) = _
  have numeric : ((BitVec.sshiftRight (4294967296 : BitVec 64) (63 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_2_5_7
example (s : riscv_state) : «dfn'SRAI» (7,1,63) (fixture s 2 4294967296) =
 (let t := fixture s 2 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (4294967296 : BitVec 64) (63 : BitVec 6).toNat), 7) (fixture s 2 4294967296) = _
  have numeric : ((BitVec.sshiftRight (4294967296 : BitVec 64) (63 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_2_6_0
example (s : riscv_state) : «dfn'SRAI» (0,1,15) (fixture s 2 9223372036854775809) =
 (let t := fixture s 2 9223372036854775809; t) := by
  change «write'GPR» ((BitVec.sshiftRight (9223372036854775809 : BitVec 64) (15 : BitVec 6).toNat), 0) (fixture s 2 9223372036854775809) = _
  have numeric : ((BitVec.sshiftRight (9223372036854775809 : BitVec 64) (15 : BitVec 6).toNat)) = (18446462598732840960 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_2_6_1
example (s : riscv_state) : «dfn'SRAI» (1,1,15) (fixture s 2 9223372036854775809) =
 (let t := fixture s 2 9223372036854775809; {t with c_gpr := holUpdate 7 (holUpdate 1 18446462598732840960 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (9223372036854775809 : BitVec 64) (15 : BitVec 6).toNat), 1) (fixture s 2 9223372036854775809) = _
  have numeric : ((BitVec.sshiftRight (9223372036854775809 : BitVec 64) (15 : BitVec 6).toNat)) = (18446462598732840960 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_2_6_7
example (s : riscv_state) : «dfn'SRAI» (7,1,15) (fixture s 2 9223372036854775809) =
 (let t := fixture s 2 9223372036854775809; {t with c_gpr := holUpdate 7 (holUpdate 7 18446462598732840960 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (9223372036854775809 : BitVec 64) (15 : BitVec 6).toNat), 7) (fixture s 2 9223372036854775809) = _
  have numeric : ((BitVec.sshiftRight (9223372036854775809 : BitVec 64) (15 : BitVec 6).toNat)) = (18446462598732840960 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_2_7_0
example (s : riscv_state) : «dfn'SRAI» (0,1,30) (fixture s 2 18446744073709551615) =
 (let t := fixture s 2 18446744073709551615; t) := by
  change «write'GPR» ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (30 : BitVec 6).toNat), 0) (fixture s 2 18446744073709551615) = _
  have numeric : ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (30 : BitVec 6).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_2_7_1
example (s : riscv_state) : «dfn'SRAI» (1,1,30) (fixture s 2 18446744073709551615) =
 (let t := fixture s 2 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (30 : BitVec 6).toNat), 1) (fixture s 2 18446744073709551615) = _
  have numeric : ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (30 : BitVec 6).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_2_7_7
example (s : riscv_state) : «dfn'SRAI» (7,1,30) (fixture s 2 18446744073709551615) =
 (let t := fixture s 2 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (30 : BitVec 6).toNat), 7) (fixture s 2 18446744073709551615) = _
  have numeric : ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (30 : BitVec 6).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_2_8_0
example (s : riscv_state) : «dfn'SRAI» (0,0,31) (fixture s 2 17) =
 (let t := fixture s 2 17; t) := by
  change «write'GPR» ((BitVec.sshiftRight (0 : BitVec 64) (31 : BitVec 6).toNat), 0) (fixture s 2 17) = _
  have numeric : ((BitVec.sshiftRight (0 : BitVec 64) (31 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_2_8_1
example (s : riscv_state) : «dfn'SRAI» (1,0,31) (fixture s 2 17) =
 (let t := fixture s 2 17; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (0 : BitVec 64) (31 : BitVec 6).toNat), 1) (fixture s 2 17) = _
  have numeric : ((BitVec.sshiftRight (0 : BitVec 64) (31 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_2_8_7
example (s : riscv_state) : «dfn'SRAI» (7,0,31) (fixture s 2 17) =
 (let t := fixture s 2 17; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (0 : BitVec 64) (31 : BitVec 6).toNat), 7) (fixture s 2 17) = _
  have numeric : ((BitVec.sshiftRight (0 : BitVec 64) (31 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_2_9_0
example (s : riscv_state) : «dfn'SRAI» (0,0,1) (fixture s 2 18446744073709551615) =
 (let t := fixture s 2 18446744073709551615; t) := by
  change «write'GPR» ((BitVec.sshiftRight (0 : BitVec 64) (1 : BitVec 6).toNat), 0) (fixture s 2 18446744073709551615) = _
  have numeric : ((BitVec.sshiftRight (0 : BitVec 64) (1 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_2_9_1
example (s : riscv_state) : «dfn'SRAI» (1,0,1) (fixture s 2 18446744073709551615) =
 (let t := fixture s 2 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (0 : BitVec 64) (1 : BitVec 6).toNat), 1) (fixture s 2 18446744073709551615) = _
  have numeric : ((BitVec.sshiftRight (0 : BitVec 64) (1 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_2_9_7
example (s : riscv_state) : «dfn'SRAI» (7,0,1) (fixture s 2 18446744073709551615) =
 (let t := fixture s 2 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (0 : BitVec 64) (1 : BitVec 6).toNat), 7) (fixture s 2 18446744073709551615) = _
  have numeric : ((BitVec.sshiftRight (0 : BitVec 64) (1 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_3_0_0
example (s : riscv_state) : «dfn'SRAI» (0,1,0) (fixture s 3 9223372036854775808) =
 (let t := fixture s 3 9223372036854775808; t) := by
  change «write'GPR» ((BitVec.sshiftRight (9223372036854775808 : BitVec 64) (0 : BitVec 6).toNat), 0) (fixture s 3 9223372036854775808) = _
  have numeric : ((BitVec.sshiftRight (9223372036854775808 : BitVec 64) (0 : BitVec 6).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_3_0_1
example (s : riscv_state) : «dfn'SRAI» (1,1,0) (fixture s 3 9223372036854775808) =
 (let t := fixture s 3 9223372036854775808; {t with c_gpr := holUpdate 7 (holUpdate 1 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (9223372036854775808 : BitVec 64) (0 : BitVec 6).toNat), 1) (fixture s 3 9223372036854775808) = _
  have numeric : ((BitVec.sshiftRight (9223372036854775808 : BitVec 64) (0 : BitVec 6).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_3_0_7
example (s : riscv_state) : «dfn'SRAI» (7,1,0) (fixture s 3 9223372036854775808) =
 (let t := fixture s 3 9223372036854775808; {t with c_gpr := holUpdate 7 (holUpdate 7 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (9223372036854775808 : BitVec 64) (0 : BitVec 6).toNat), 7) (fixture s 3 9223372036854775808) = _
  have numeric : ((BitVec.sshiftRight (9223372036854775808 : BitVec 64) (0 : BitVec 6).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_3_1_0
example (s : riscv_state) : «dfn'SRAI» (0,1,1) (fixture s 3 2147483649) =
 (let t := fixture s 3 2147483649; t) := by
  change «write'GPR» ((BitVec.sshiftRight (2147483649 : BitVec 64) (1 : BitVec 6).toNat), 0) (fixture s 3 2147483649) = _
  have numeric : ((BitVec.sshiftRight (2147483649 : BitVec 64) (1 : BitVec 6).toNat)) = (1073741824 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_3_1_1
example (s : riscv_state) : «dfn'SRAI» (1,1,1) (fixture s 3 2147483649) =
 (let t := fixture s 3 2147483649; {t with c_gpr := holUpdate 7 (holUpdate 1 1073741824 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (2147483649 : BitVec 64) (1 : BitVec 6).toNat), 1) (fixture s 3 2147483649) = _
  have numeric : ((BitVec.sshiftRight (2147483649 : BitVec 64) (1 : BitVec 6).toNat)) = (1073741824 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_3_1_7
example (s : riscv_state) : «dfn'SRAI» (7,1,1) (fixture s 3 2147483649) =
 (let t := fixture s 3 2147483649; {t with c_gpr := holUpdate 7 (holUpdate 7 1073741824 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (2147483649 : BitVec 64) (1 : BitVec 6).toNat), 7) (fixture s 3 2147483649) = _
  have numeric : ((BitVec.sshiftRight (2147483649 : BitVec 64) (1 : BitVec 6).toNat)) = (1073741824 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_3_2_0
example (s : riscv_state) : «dfn'SRAI» (0,1,31) (fixture s 3 4294967297) =
 (let t := fixture s 3 4294967297; t) := by
  change «write'GPR» ((BitVec.sshiftRight (4294967297 : BitVec 64) (31 : BitVec 6).toNat), 0) (fixture s 3 4294967297) = _
  have numeric : ((BitVec.sshiftRight (4294967297 : BitVec 64) (31 : BitVec 6).toNat)) = (2 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_3_2_1
example (s : riscv_state) : «dfn'SRAI» (1,1,31) (fixture s 3 4294967297) =
 (let t := fixture s 3 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 1 2 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (4294967297 : BitVec 64) (31 : BitVec 6).toNat), 1) (fixture s 3 4294967297) = _
  have numeric : ((BitVec.sshiftRight (4294967297 : BitVec 64) (31 : BitVec 6).toNat)) = (2 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_3_2_7
example (s : riscv_state) : «dfn'SRAI» (7,1,31) (fixture s 3 4294967297) =
 (let t := fixture s 3 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 7 2 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (4294967297 : BitVec 64) (31 : BitVec 6).toNat), 7) (fixture s 3 4294967297) = _
  have numeric : ((BitVec.sshiftRight (4294967297 : BitVec 64) (31 : BitVec 6).toNat)) = (2 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_3_3_0
example (s : riscv_state) : «dfn'SRAI» (0,1,32) (fixture s 3 18446744073709551615) =
 (let t := fixture s 3 18446744073709551615; t) := by
  change «write'GPR» ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (32 : BitVec 6).toNat), 0) (fixture s 3 18446744073709551615) = _
  have numeric : ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (32 : BitVec 6).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_3_3_1
example (s : riscv_state) : «dfn'SRAI» (1,1,32) (fixture s 3 18446744073709551615) =
 (let t := fixture s 3 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (32 : BitVec 6).toNat), 1) (fixture s 3 18446744073709551615) = _
  have numeric : ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (32 : BitVec 6).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_3_3_7
example (s : riscv_state) : «dfn'SRAI» (7,1,32) (fixture s 3 18446744073709551615) =
 (let t := fixture s 3 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (32 : BitVec 6).toNat), 7) (fixture s 3 18446744073709551615) = _
  have numeric : ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (32 : BitVec 6).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_3_4_0
example (s : riscv_state) : «dfn'SRAI» (0,1,33) (fixture s 3 2147483648) =
 (let t := fixture s 3 2147483648; t) := by
  change «write'GPR» ((BitVec.sshiftRight (2147483648 : BitVec 64) (33 : BitVec 6).toNat), 0) (fixture s 3 2147483648) = _
  have numeric : ((BitVec.sshiftRight (2147483648 : BitVec 64) (33 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_3_4_1
example (s : riscv_state) : «dfn'SRAI» (1,1,33) (fixture s 3 2147483648) =
 (let t := fixture s 3 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (2147483648 : BitVec 64) (33 : BitVec 6).toNat), 1) (fixture s 3 2147483648) = _
  have numeric : ((BitVec.sshiftRight (2147483648 : BitVec 64) (33 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_3_4_7
example (s : riscv_state) : «dfn'SRAI» (7,1,33) (fixture s 3 2147483648) =
 (let t := fixture s 3 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (2147483648 : BitVec 64) (33 : BitVec 6).toNat), 7) (fixture s 3 2147483648) = _
  have numeric : ((BitVec.sshiftRight (2147483648 : BitVec 64) (33 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_3_5_0
example (s : riscv_state) : «dfn'SRAI» (0,1,63) (fixture s 3 4294967296) =
 (let t := fixture s 3 4294967296; t) := by
  change «write'GPR» ((BitVec.sshiftRight (4294967296 : BitVec 64) (63 : BitVec 6).toNat), 0) (fixture s 3 4294967296) = _
  have numeric : ((BitVec.sshiftRight (4294967296 : BitVec 64) (63 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_3_5_1
example (s : riscv_state) : «dfn'SRAI» (1,1,63) (fixture s 3 4294967296) =
 (let t := fixture s 3 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (4294967296 : BitVec 64) (63 : BitVec 6).toNat), 1) (fixture s 3 4294967296) = _
  have numeric : ((BitVec.sshiftRight (4294967296 : BitVec 64) (63 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_3_5_7
example (s : riscv_state) : «dfn'SRAI» (7,1,63) (fixture s 3 4294967296) =
 (let t := fixture s 3 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (4294967296 : BitVec 64) (63 : BitVec 6).toNat), 7) (fixture s 3 4294967296) = _
  have numeric : ((BitVec.sshiftRight (4294967296 : BitVec 64) (63 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_3_6_0
example (s : riscv_state) : «dfn'SRAI» (0,1,15) (fixture s 3 9223372036854775809) =
 (let t := fixture s 3 9223372036854775809; t) := by
  change «write'GPR» ((BitVec.sshiftRight (9223372036854775809 : BitVec 64) (15 : BitVec 6).toNat), 0) (fixture s 3 9223372036854775809) = _
  have numeric : ((BitVec.sshiftRight (9223372036854775809 : BitVec 64) (15 : BitVec 6).toNat)) = (18446462598732840960 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_3_6_1
example (s : riscv_state) : «dfn'SRAI» (1,1,15) (fixture s 3 9223372036854775809) =
 (let t := fixture s 3 9223372036854775809; {t with c_gpr := holUpdate 7 (holUpdate 1 18446462598732840960 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (9223372036854775809 : BitVec 64) (15 : BitVec 6).toNat), 1) (fixture s 3 9223372036854775809) = _
  have numeric : ((BitVec.sshiftRight (9223372036854775809 : BitVec 64) (15 : BitVec 6).toNat)) = (18446462598732840960 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_3_6_7
example (s : riscv_state) : «dfn'SRAI» (7,1,15) (fixture s 3 9223372036854775809) =
 (let t := fixture s 3 9223372036854775809; {t with c_gpr := holUpdate 7 (holUpdate 7 18446462598732840960 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (9223372036854775809 : BitVec 64) (15 : BitVec 6).toNat), 7) (fixture s 3 9223372036854775809) = _
  have numeric : ((BitVec.sshiftRight (9223372036854775809 : BitVec 64) (15 : BitVec 6).toNat)) = (18446462598732840960 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_3_7_0
example (s : riscv_state) : «dfn'SRAI» (0,1,30) (fixture s 3 18446744073709551615) =
 (let t := fixture s 3 18446744073709551615; t) := by
  change «write'GPR» ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (30 : BitVec 6).toNat), 0) (fixture s 3 18446744073709551615) = _
  have numeric : ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (30 : BitVec 6).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_3_7_1
example (s : riscv_state) : «dfn'SRAI» (1,1,30) (fixture s 3 18446744073709551615) =
 (let t := fixture s 3 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (30 : BitVec 6).toNat), 1) (fixture s 3 18446744073709551615) = _
  have numeric : ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (30 : BitVec 6).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_3_7_7
example (s : riscv_state) : «dfn'SRAI» (7,1,30) (fixture s 3 18446744073709551615) =
 (let t := fixture s 3 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (30 : BitVec 6).toNat), 7) (fixture s 3 18446744073709551615) = _
  have numeric : ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (30 : BitVec 6).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_3_8_0
example (s : riscv_state) : «dfn'SRAI» (0,0,31) (fixture s 3 17) =
 (let t := fixture s 3 17; t) := by
  change «write'GPR» ((BitVec.sshiftRight (0 : BitVec 64) (31 : BitVec 6).toNat), 0) (fixture s 3 17) = _
  have numeric : ((BitVec.sshiftRight (0 : BitVec 64) (31 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_3_8_1
example (s : riscv_state) : «dfn'SRAI» (1,0,31) (fixture s 3 17) =
 (let t := fixture s 3 17; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (0 : BitVec 64) (31 : BitVec 6).toNat), 1) (fixture s 3 17) = _
  have numeric : ((BitVec.sshiftRight (0 : BitVec 64) (31 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_3_8_7
example (s : riscv_state) : «dfn'SRAI» (7,0,31) (fixture s 3 17) =
 (let t := fixture s 3 17; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (0 : BitVec 64) (31 : BitVec 6).toNat), 7) (fixture s 3 17) = _
  have numeric : ((BitVec.sshiftRight (0 : BitVec 64) (31 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_3_9_0
example (s : riscv_state) : «dfn'SRAI» (0,0,1) (fixture s 3 18446744073709551615) =
 (let t := fixture s 3 18446744073709551615; t) := by
  change «write'GPR» ((BitVec.sshiftRight (0 : BitVec 64) (1 : BitVec 6).toNat), 0) (fixture s 3 18446744073709551615) = _
  have numeric : ((BitVec.sshiftRight (0 : BitVec 64) (1 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_3_9_1
example (s : riscv_state) : «dfn'SRAI» (1,0,1) (fixture s 3 18446744073709551615) =
 (let t := fixture s 3 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (0 : BitVec 64) (1 : BitVec 6).toNat), 1) (fixture s 3 18446744073709551615) = _
  have numeric : ((BitVec.sshiftRight (0 : BitVec 64) (1 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_SRAI_3_9_7
example (s : riscv_state) : «dfn'SRAI» (7,0,1) (fixture s 3 18446744073709551615) =
 (let t := fixture s 3 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (0 : BitVec 64) (1 : BitVec 6).toNat), 7) (fixture s 3 18446744073709551615) = _
  have numeric : ((BitVec.sshiftRight (0 : BitVec 64) (1 : BitVec 6).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- immediate_shift_symbolic_SLLI
example (s : riscv_state) : «dfn'SLLI» (0,0,32) ({fixture s 1 17 with exception := exception.NoException}) =
 (match in32BitMode () ({fixture s 1 17 with exception := exception.NoException}) with | (v,u) => if v && (32 : BitVec 6).getLsbD 5 then signalException ExceptionType.Illegal_Instr u else u) := by rfl

-- immediate_shift_symbolic_SRLI
example (s : riscv_state) : «dfn'SRLI» (0,0,32) ({fixture s 1 17 with exception := exception.NoException}) =
 (match in32BitMode () ({fixture s 1 17 with exception := exception.NoException}) with | (v,u) => if v && (32 : BitVec 6).getLsbD 5 then signalException ExceptionType.Illegal_Instr u else (match in32BitMode () u with | (_,u1) => u1)) := by rfl

-- immediate_shift_symbolic_SRAI
example (s : riscv_state) : «dfn'SRAI» (0,0,32) ({fixture s 1 17 with exception := exception.NoException}) =
 (match in32BitMode () ({fixture s 1 17 with exception := exception.NoException}) with | (v,u) => if v && (32 : BitVec 6).getLsbD 5 then signalException ExceptionType.Illegal_Instr u else (match in32BitMode () u with | (_,u1) => u1)) := by rfl

private def unknownMessage : List (BitVec 8) :=
 [85,110,107,110,111,119,110,32,97,114,99,104,105,116,101,99,116,117,114,101,58,32,49]

-- immediate_shift_invalid_SLLI_0_0
example (s : riscv_state) : «dfn'SLLI» (0,0,0) ({fixture s 1 17 with exception := exception.NoException}) =
 (let t := {fixture s 1 17 with exception := exception.NoException}; let u := {t with exception := exception.UNDEFINED unknownMessage}; u) := by
  simp [«dfn'SLLI», fixture, in32BitMode, curArch, architecture, MCSR, raiseException_eq, unknownMessage, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, «write'GPR»]
  all_goals (split <;> rfl)

-- immediate_shift_invalid_SLLI_0_1
example (s : riscv_state) : «dfn'SLLI» (1,0,0) ({fixture s 1 17 with exception := exception.NoException}) =
 (let t := {fixture s 1 17 with exception := exception.NoException}; let u := {t with exception := exception.UNDEFINED unknownMessage}; {u with c_gpr := holUpdate 7 (holUpdate 1 0 (u.c_gpr 7)) u.c_gpr}) := by
  simp [«dfn'SLLI», fixture, in32BitMode, curArch, architecture, MCSR, GPR, raiseException_eq, unknownMessage, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, «write'GPR», «write'gpr»]
  all_goals (split <;> rfl)

-- immediate_shift_invalid_SLLI_1_0
example (s : riscv_state) : «dfn'SLLI» (0,0,0) ({fixture s 1 17 with exception := exception.UNDEFINED [9]}) =
 (let t := {fixture s 1 17 with exception := exception.UNDEFINED [9]}; let u := {t with exception := exception.UNDEFINED [9]}; u) := by
  simp [«dfn'SLLI», fixture, in32BitMode, curArch, architecture, MCSR, raiseException_eq, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, «write'GPR»]
  all_goals (split <;> rfl)

-- immediate_shift_invalid_SLLI_1_1
example (s : riscv_state) : «dfn'SLLI» (1,0,0) ({fixture s 1 17 with exception := exception.UNDEFINED [9]}) =
 (let t := {fixture s 1 17 with exception := exception.UNDEFINED [9]}; let u := {t with exception := exception.UNDEFINED [9]}; {u with c_gpr := holUpdate 7 (holUpdate 1 0 (u.c_gpr 7)) u.c_gpr}) := by
  simp [«dfn'SLLI», fixture, in32BitMode, curArch, architecture, MCSR, GPR, raiseException_eq, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, «write'GPR», «write'gpr»]
  all_goals (split <;> rfl)

-- immediate_shift_invalid_SRLI_0_0
example (s : riscv_state) : «dfn'SRLI» (0,0,0) ({fixture s 1 17 with exception := exception.NoException}) =
 (let t := {fixture s 1 17 with exception := exception.NoException}; let u := {t with exception := exception.UNDEFINED unknownMessage}; u) := by
  simp [«dfn'SRLI», fixture, in32BitMode, curArch, architecture, MCSR, raiseException_eq, unknownMessage, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, «write'GPR»]
  all_goals (split <;> rfl)

-- immediate_shift_invalid_SRLI_0_1
example (s : riscv_state) : «dfn'SRLI» (1,0,0) ({fixture s 1 17 with exception := exception.NoException}) =
 (let t := {fixture s 1 17 with exception := exception.NoException}; let u := {t with exception := exception.UNDEFINED unknownMessage}; {u with c_gpr := holUpdate 7 (holUpdate 1 0 (u.c_gpr 7)) u.c_gpr}) := by
  simp [«dfn'SRLI», fixture, in32BitMode, curArch, architecture, MCSR, GPR, raiseException_eq, unknownMessage, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, «write'GPR», «write'gpr»]
  all_goals (split <;> rfl)

-- immediate_shift_invalid_SRLI_1_0
example (s : riscv_state) : «dfn'SRLI» (0,0,0) ({fixture s 1 17 with exception := exception.UNDEFINED [9]}) =
 (let t := {fixture s 1 17 with exception := exception.UNDEFINED [9]}; let u := {t with exception := exception.UNDEFINED [9]}; u) := by
  simp [«dfn'SRLI», fixture, in32BitMode, curArch, architecture, MCSR, raiseException_eq, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, «write'GPR»]
  all_goals (split <;> rfl)

-- immediate_shift_invalid_SRLI_1_1
example (s : riscv_state) : «dfn'SRLI» (1,0,0) ({fixture s 1 17 with exception := exception.UNDEFINED [9]}) =
 (let t := {fixture s 1 17 with exception := exception.UNDEFINED [9]}; let u := {t with exception := exception.UNDEFINED [9]}; {u with c_gpr := holUpdate 7 (holUpdate 1 0 (u.c_gpr 7)) u.c_gpr}) := by
  simp [«dfn'SRLI», fixture, in32BitMode, curArch, architecture, MCSR, GPR, raiseException_eq, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, «write'GPR», «write'gpr»]
  all_goals (split <;> rfl)

-- immediate_shift_invalid_SRAI_0_0
example (s : riscv_state) : «dfn'SRAI» (0,0,0) ({fixture s 1 17 with exception := exception.NoException}) =
 (let t := {fixture s 1 17 with exception := exception.NoException}; let u := {t with exception := exception.UNDEFINED unknownMessage}; u) := by
  simp [«dfn'SRAI», fixture, in32BitMode, curArch, architecture, MCSR, raiseException_eq, unknownMessage, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, «write'GPR»]
  all_goals (split <;> rfl)

-- immediate_shift_invalid_SRAI_0_1
example (s : riscv_state) : «dfn'SRAI» (1,0,0) ({fixture s 1 17 with exception := exception.NoException}) =
 (let t := {fixture s 1 17 with exception := exception.NoException}; let u := {t with exception := exception.UNDEFINED unknownMessage}; {u with c_gpr := holUpdate 7 (holUpdate 1 0 (u.c_gpr 7)) u.c_gpr}) := by
  simp [«dfn'SRAI», fixture, in32BitMode, curArch, architecture, MCSR, GPR, raiseException_eq, unknownMessage, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, «write'GPR», «write'gpr»]
  all_goals (split <;> rfl)

-- immediate_shift_invalid_SRAI_1_0
example (s : riscv_state) : «dfn'SRAI» (0,0,0) ({fixture s 1 17 with exception := exception.UNDEFINED [9]}) =
 (let t := {fixture s 1 17 with exception := exception.UNDEFINED [9]}; let u := {t with exception := exception.UNDEFINED [9]}; u) := by
  simp [«dfn'SRAI», fixture, in32BitMode, curArch, architecture, MCSR, raiseException_eq, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, «write'GPR»]
  all_goals (split <;> rfl)

-- immediate_shift_invalid_SRAI_1_1
example (s : riscv_state) : «dfn'SRAI» (1,0,0) ({fixture s 1 17 with exception := exception.UNDEFINED [9]}) =
 (let t := {fixture s 1 17 with exception := exception.UNDEFINED [9]}; let u := {t with exception := exception.UNDEFINED [9]}; {u with c_gpr := holUpdate 7 (holUpdate 1 0 (u.c_gpr 7)) u.c_gpr}) := by
  simp [«dfn'SRAI», fixture, in32BitMode, curArch, architecture, MCSR, GPR, raiseException_eq, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, «write'GPR», «write'gpr»]
  all_goals (split <;> rfl)

end Flapjack.Test.L3ImmediateShiftParity
