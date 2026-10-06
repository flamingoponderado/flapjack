import Flapjack.RiscV.L3.Defs.Multiply
set_option maxRecDepth 20000
namespace Flapjack.Test.L3MultiplyParity
open Flapjack.RiscV.L3
private def fixture (s : riscv_state) (mode : BitVec 2) (a b : BitVec 64) : riscv_state :=
 {s with procID := 7, c_MCSR := fun id => {s.c_MCSR id with mcpuid := {(s.c_MCSR id).mcpuid with ArchBase := mode}}, c_gpr := fun id r => if r = 1 then a else if r = 2 then b else s.c_gpr id r}

-- multiply_MUL_0_0_0
example (s : riscv_state) : «dfn'MUL» (0,1,2) (fixture s 0 0 0) = (let t := fixture s 0 0 0; t) := by
 change «write'GPR» (((0 : BitVec 64) * (0 : BitVec 64)), 0) (fixture s 0 0 0) = _
 have numeric : (((0 : BitVec 64) * (0 : BitVec 64))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_0_0_1
example (s : riscv_state) : «dfn'MUL» (1,1,2) (fixture s 0 0 0) = (let t := fixture s 0 0 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((0 : BitVec 64) * (0 : BitVec 64)), 1) (fixture s 0 0 0) = _
 have numeric : (((0 : BitVec 64) * (0 : BitVec 64))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_0_0_2
example (s : riscv_state) : «dfn'MUL» (2,1,2) (fixture s 0 0 0) = (let t := fixture s 0 0 0; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((0 : BitVec 64) * (0 : BitVec 64)), 2) (fixture s 0 0 0) = _
 have numeric : (((0 : BitVec 64) * (0 : BitVec 64))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_0_0_7
example (s : riscv_state) : «dfn'MUL» (7,1,2) (fixture s 0 0 0) = (let t := fixture s 0 0 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((0 : BitVec 64) * (0 : BitVec 64)), 7) (fixture s 0 0 0) = _
 have numeric : (((0 : BitVec 64) * (0 : BitVec 64))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_0_1_0
example (s : riscv_state) : «dfn'MUL» (0,1,2) (fixture s 0 18446744073709551615 18446744073709551615) = (let t := fixture s 0 18446744073709551615 18446744073709551615; t) := by
 change «write'GPR» (((18446744073709551615 : BitVec 64) * (18446744073709551615 : BitVec 64)), 0) (fixture s 0 18446744073709551615 18446744073709551615) = _
 have numeric : (((18446744073709551615 : BitVec 64) * (18446744073709551615 : BitVec 64))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_0_1_1
example (s : riscv_state) : «dfn'MUL» (1,1,2) (fixture s 0 18446744073709551615 18446744073709551615) = (let t := fixture s 0 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((18446744073709551615 : BitVec 64) * (18446744073709551615 : BitVec 64)), 1) (fixture s 0 18446744073709551615 18446744073709551615) = _
 have numeric : (((18446744073709551615 : BitVec 64) * (18446744073709551615 : BitVec 64))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_0_1_2
example (s : riscv_state) : «dfn'MUL» (2,1,2) (fixture s 0 18446744073709551615 18446744073709551615) = (let t := fixture s 0 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((18446744073709551615 : BitVec 64) * (18446744073709551615 : BitVec 64)), 2) (fixture s 0 18446744073709551615 18446744073709551615) = _
 have numeric : (((18446744073709551615 : BitVec 64) * (18446744073709551615 : BitVec 64))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_0_1_7
example (s : riscv_state) : «dfn'MUL» (7,1,2) (fixture s 0 18446744073709551615 18446744073709551615) = (let t := fixture s 0 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((18446744073709551615 : BitVec 64) * (18446744073709551615 : BitVec 64)), 7) (fixture s 0 18446744073709551615 18446744073709551615) = _
 have numeric : (((18446744073709551615 : BitVec 64) * (18446744073709551615 : BitVec 64))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_0_2_0
example (s : riscv_state) : «dfn'MUL» (0,1,2) (fixture s 0 18446744073709551615 2) = (let t := fixture s 0 18446744073709551615 2; t) := by
 change «write'GPR» (((18446744073709551615 : BitVec 64) * (2 : BitVec 64)), 0) (fixture s 0 18446744073709551615 2) = _
 have numeric : (((18446744073709551615 : BitVec 64) * (2 : BitVec 64))) = (18446744073709551614 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_0_2_1
example (s : riscv_state) : «dfn'MUL» (1,1,2) (fixture s 0 18446744073709551615 2) = (let t := fixture s 0 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((18446744073709551615 : BitVec 64) * (2 : BitVec 64)), 1) (fixture s 0 18446744073709551615 2) = _
 have numeric : (((18446744073709551615 : BitVec 64) * (2 : BitVec 64))) = (18446744073709551614 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_0_2_2
example (s : riscv_state) : «dfn'MUL» (2,1,2) (fixture s 0 18446744073709551615 2) = (let t := fixture s 0 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((18446744073709551615 : BitVec 64) * (2 : BitVec 64)), 2) (fixture s 0 18446744073709551615 2) = _
 have numeric : (((18446744073709551615 : BitVec 64) * (2 : BitVec 64))) = (18446744073709551614 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_0_2_7
example (s : riscv_state) : «dfn'MUL» (7,1,2) (fixture s 0 18446744073709551615 2) = (let t := fixture s 0 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((18446744073709551615 : BitVec 64) * (2 : BitVec 64)), 7) (fixture s 0 18446744073709551615 2) = _
 have numeric : (((18446744073709551615 : BitVec 64) * (2 : BitVec 64))) = (18446744073709551614 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_0_3_0
example (s : riscv_state) : «dfn'MUL» (0,1,2) (fixture s 0 2147483648 2147483648) = (let t := fixture s 0 2147483648 2147483648; t) := by
 change «write'GPR» (((2147483648 : BitVec 64) * (2147483648 : BitVec 64)), 0) (fixture s 0 2147483648 2147483648) = _
 have numeric : (((2147483648 : BitVec 64) * (2147483648 : BitVec 64))) = (4611686018427387904 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_0_3_1
example (s : riscv_state) : «dfn'MUL» (1,1,2) (fixture s 0 2147483648 2147483648) = (let t := fixture s 0 2147483648 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 1 4611686018427387904 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((2147483648 : BitVec 64) * (2147483648 : BitVec 64)), 1) (fixture s 0 2147483648 2147483648) = _
 have numeric : (((2147483648 : BitVec 64) * (2147483648 : BitVec 64))) = (4611686018427387904 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_0_3_2
example (s : riscv_state) : «dfn'MUL» (2,1,2) (fixture s 0 2147483648 2147483648) = (let t := fixture s 0 2147483648 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 2 4611686018427387904 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((2147483648 : BitVec 64) * (2147483648 : BitVec 64)), 2) (fixture s 0 2147483648 2147483648) = _
 have numeric : (((2147483648 : BitVec 64) * (2147483648 : BitVec 64))) = (4611686018427387904 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_0_3_7
example (s : riscv_state) : «dfn'MUL» (7,1,2) (fixture s 0 2147483648 2147483648) = (let t := fixture s 0 2147483648 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 7 4611686018427387904 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((2147483648 : BitVec 64) * (2147483648 : BitVec 64)), 7) (fixture s 0 2147483648 2147483648) = _
 have numeric : (((2147483648 : BitVec 64) * (2147483648 : BitVec 64))) = (4611686018427387904 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_0_4_0
example (s : riscv_state) : «dfn'MUL» (0,1,2) (fixture s 0 4294967295 4294967295) = (let t := fixture s 0 4294967295 4294967295; t) := by
 change «write'GPR» (((4294967295 : BitVec 64) * (4294967295 : BitVec 64)), 0) (fixture s 0 4294967295 4294967295) = _
 have numeric : (((4294967295 : BitVec 64) * (4294967295 : BitVec 64))) = (18446744065119617025 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_0_4_1
example (s : riscv_state) : «dfn'MUL» (1,1,2) (fixture s 0 4294967295 4294967295) = (let t := fixture s 0 4294967295 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744065119617025 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((4294967295 : BitVec 64) * (4294967295 : BitVec 64)), 1) (fixture s 0 4294967295 4294967295) = _
 have numeric : (((4294967295 : BitVec 64) * (4294967295 : BitVec 64))) = (18446744065119617025 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_0_4_2
example (s : riscv_state) : «dfn'MUL» (2,1,2) (fixture s 0 4294967295 4294967295) = (let t := fixture s 0 4294967295 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744065119617025 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((4294967295 : BitVec 64) * (4294967295 : BitVec 64)), 2) (fixture s 0 4294967295 4294967295) = _
 have numeric : (((4294967295 : BitVec 64) * (4294967295 : BitVec 64))) = (18446744065119617025 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_0_4_7
example (s : riscv_state) : «dfn'MUL» (7,1,2) (fixture s 0 4294967295 4294967295) = (let t := fixture s 0 4294967295 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744065119617025 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((4294967295 : BitVec 64) * (4294967295 : BitVec 64)), 7) (fixture s 0 4294967295 4294967295) = _
 have numeric : (((4294967295 : BitVec 64) * (4294967295 : BitVec 64))) = (18446744065119617025 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_0_5_0
example (s : riscv_state) : «dfn'MUL» (0,1,2) (fixture s 0 9223372036854775808 2) = (let t := fixture s 0 9223372036854775808 2; t) := by
 change «write'GPR» (((9223372036854775808 : BitVec 64) * (2 : BitVec 64)), 0) (fixture s 0 9223372036854775808 2) = _
 have numeric : (((9223372036854775808 : BitVec 64) * (2 : BitVec 64))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_0_5_1
example (s : riscv_state) : «dfn'MUL» (1,1,2) (fixture s 0 9223372036854775808 2) = (let t := fixture s 0 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((9223372036854775808 : BitVec 64) * (2 : BitVec 64)), 1) (fixture s 0 9223372036854775808 2) = _
 have numeric : (((9223372036854775808 : BitVec 64) * (2 : BitVec 64))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_0_5_2
example (s : riscv_state) : «dfn'MUL» (2,1,2) (fixture s 0 9223372036854775808 2) = (let t := fixture s 0 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((9223372036854775808 : BitVec 64) * (2 : BitVec 64)), 2) (fixture s 0 9223372036854775808 2) = _
 have numeric : (((9223372036854775808 : BitVec 64) * (2 : BitVec 64))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_0_5_7
example (s : riscv_state) : «dfn'MUL» (7,1,2) (fixture s 0 9223372036854775808 2) = (let t := fixture s 0 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((9223372036854775808 : BitVec 64) * (2 : BitVec 64)), 7) (fixture s 0 9223372036854775808 2) = _
 have numeric : (((9223372036854775808 : BitVec 64) * (2 : BitVec 64))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_0_6_0
example (s : riscv_state) : «dfn'MUL» (0,1,2) (fixture s 0 9223372036854775808 18446744073709551615) = (let t := fixture s 0 9223372036854775808 18446744073709551615; t) := by
 change «write'GPR» (((9223372036854775808 : BitVec 64) * (18446744073709551615 : BitVec 64)), 0) (fixture s 0 9223372036854775808 18446744073709551615) = _
 have numeric : (((9223372036854775808 : BitVec 64) * (18446744073709551615 : BitVec 64))) = (9223372036854775808 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_0_6_1
example (s : riscv_state) : «dfn'MUL» (1,1,2) (fixture s 0 9223372036854775808 18446744073709551615) = (let t := fixture s 0 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((9223372036854775808 : BitVec 64) * (18446744073709551615 : BitVec 64)), 1) (fixture s 0 9223372036854775808 18446744073709551615) = _
 have numeric : (((9223372036854775808 : BitVec 64) * (18446744073709551615 : BitVec 64))) = (9223372036854775808 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_0_6_2
example (s : riscv_state) : «dfn'MUL» (2,1,2) (fixture s 0 9223372036854775808 18446744073709551615) = (let t := fixture s 0 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((9223372036854775808 : BitVec 64) * (18446744073709551615 : BitVec 64)), 2) (fixture s 0 9223372036854775808 18446744073709551615) = _
 have numeric : (((9223372036854775808 : BitVec 64) * (18446744073709551615 : BitVec 64))) = (9223372036854775808 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_0_6_7
example (s : riscv_state) : «dfn'MUL» (7,1,2) (fixture s 0 9223372036854775808 18446744073709551615) = (let t := fixture s 0 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((9223372036854775808 : BitVec 64) * (18446744073709551615 : BitVec 64)), 7) (fixture s 0 9223372036854775808 18446744073709551615) = _
 have numeric : (((9223372036854775808 : BitVec 64) * (18446744073709551615 : BitVec 64))) = (9223372036854775808 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_0_7_0
example (s : riscv_state) : «dfn'MUL» (0,1,2) (fixture s 0 9223372036854775807 9223372036854775807) = (let t := fixture s 0 9223372036854775807 9223372036854775807; t) := by
 change «write'GPR» (((9223372036854775807 : BitVec 64) * (9223372036854775807 : BitVec 64)), 0) (fixture s 0 9223372036854775807 9223372036854775807) = _
 have numeric : (((9223372036854775807 : BitVec 64) * (9223372036854775807 : BitVec 64))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_0_7_1
example (s : riscv_state) : «dfn'MUL» (1,1,2) (fixture s 0 9223372036854775807 9223372036854775807) = (let t := fixture s 0 9223372036854775807 9223372036854775807; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((9223372036854775807 : BitVec 64) * (9223372036854775807 : BitVec 64)), 1) (fixture s 0 9223372036854775807 9223372036854775807) = _
 have numeric : (((9223372036854775807 : BitVec 64) * (9223372036854775807 : BitVec 64))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_0_7_2
example (s : riscv_state) : «dfn'MUL» (2,1,2) (fixture s 0 9223372036854775807 9223372036854775807) = (let t := fixture s 0 9223372036854775807 9223372036854775807; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((9223372036854775807 : BitVec 64) * (9223372036854775807 : BitVec 64)), 2) (fixture s 0 9223372036854775807 9223372036854775807) = _
 have numeric : (((9223372036854775807 : BitVec 64) * (9223372036854775807 : BitVec 64))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_0_7_7
example (s : riscv_state) : «dfn'MUL» (7,1,2) (fixture s 0 9223372036854775807 9223372036854775807) = (let t := fixture s 0 9223372036854775807 9223372036854775807; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((9223372036854775807 : BitVec 64) * (9223372036854775807 : BitVec 64)), 7) (fixture s 0 9223372036854775807 9223372036854775807) = _
 have numeric : (((9223372036854775807 : BitVec 64) * (9223372036854775807 : BitVec 64))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_0_8_0
example (s : riscv_state) : «dfn'MUL» (0,1,2) (fixture s 0 4294967297 4294967297) = (let t := fixture s 0 4294967297 4294967297; t) := by
 change «write'GPR» (((4294967297 : BitVec 64) * (4294967297 : BitVec 64)), 0) (fixture s 0 4294967297 4294967297) = _
 have numeric : (((4294967297 : BitVec 64) * (4294967297 : BitVec 64))) = (8589934593 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_0_8_1
example (s : riscv_state) : «dfn'MUL» (1,1,2) (fixture s 0 4294967297 4294967297) = (let t := fixture s 0 4294967297 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 1 8589934593 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((4294967297 : BitVec 64) * (4294967297 : BitVec 64)), 1) (fixture s 0 4294967297 4294967297) = _
 have numeric : (((4294967297 : BitVec 64) * (4294967297 : BitVec 64))) = (8589934593 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_0_8_2
example (s : riscv_state) : «dfn'MUL» (2,1,2) (fixture s 0 4294967297 4294967297) = (let t := fixture s 0 4294967297 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 2 8589934593 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((4294967297 : BitVec 64) * (4294967297 : BitVec 64)), 2) (fixture s 0 4294967297 4294967297) = _
 have numeric : (((4294967297 : BitVec 64) * (4294967297 : BitVec 64))) = (8589934593 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_0_8_7
example (s : riscv_state) : «dfn'MUL» (7,1,2) (fixture s 0 4294967297 4294967297) = (let t := fixture s 0 4294967297 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 7 8589934593 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((4294967297 : BitVec 64) * (4294967297 : BitVec 64)), 7) (fixture s 0 4294967297 4294967297) = _
 have numeric : (((4294967297 : BitVec 64) * (4294967297 : BitVec 64))) = (8589934593 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_0_9_0
example (s : riscv_state) : «dfn'MUL» (0,0,2) (fixture s 0 17 18446744073709551615) = (let t := fixture s 0 17 18446744073709551615; t) := by
 change «write'GPR» (((0 : BitVec 64) * (18446744073709551615 : BitVec 64)), 0) (fixture s 0 17 18446744073709551615) = _
 have numeric : (((0 : BitVec 64) * (18446744073709551615 : BitVec 64))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_0_9_1
example (s : riscv_state) : «dfn'MUL» (1,0,2) (fixture s 0 17 18446744073709551615) = (let t := fixture s 0 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((0 : BitVec 64) * (18446744073709551615 : BitVec 64)), 1) (fixture s 0 17 18446744073709551615) = _
 have numeric : (((0 : BitVec 64) * (18446744073709551615 : BitVec 64))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_0_9_2
example (s : riscv_state) : «dfn'MUL» (2,0,2) (fixture s 0 17 18446744073709551615) = (let t := fixture s 0 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((0 : BitVec 64) * (18446744073709551615 : BitVec 64)), 2) (fixture s 0 17 18446744073709551615) = _
 have numeric : (((0 : BitVec 64) * (18446744073709551615 : BitVec 64))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_0_9_7
example (s : riscv_state) : «dfn'MUL» (7,0,2) (fixture s 0 17 18446744073709551615) = (let t := fixture s 0 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((0 : BitVec 64) * (18446744073709551615 : BitVec 64)), 7) (fixture s 0 17 18446744073709551615) = _
 have numeric : (((0 : BitVec 64) * (18446744073709551615 : BitVec 64))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_0_10_0
example (s : riscv_state) : «dfn'MUL» (0,1,0) (fixture s 0 18446744073709551615 17) = (let t := fixture s 0 18446744073709551615 17; t) := by
 change «write'GPR» (((18446744073709551615 : BitVec 64) * (0 : BitVec 64)), 0) (fixture s 0 18446744073709551615 17) = _
 have numeric : (((18446744073709551615 : BitVec 64) * (0 : BitVec 64))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_0_10_1
example (s : riscv_state) : «dfn'MUL» (1,1,0) (fixture s 0 18446744073709551615 17) = (let t := fixture s 0 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((18446744073709551615 : BitVec 64) * (0 : BitVec 64)), 1) (fixture s 0 18446744073709551615 17) = _
 have numeric : (((18446744073709551615 : BitVec 64) * (0 : BitVec 64))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_0_10_2
example (s : riscv_state) : «dfn'MUL» (2,1,0) (fixture s 0 18446744073709551615 17) = (let t := fixture s 0 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((18446744073709551615 : BitVec 64) * (0 : BitVec 64)), 2) (fixture s 0 18446744073709551615 17) = _
 have numeric : (((18446744073709551615 : BitVec 64) * (0 : BitVec 64))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_0_10_7
example (s : riscv_state) : «dfn'MUL» (7,1,0) (fixture s 0 18446744073709551615 17) = (let t := fixture s 0 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((18446744073709551615 : BitVec 64) * (0 : BitVec 64)), 7) (fixture s 0 18446744073709551615 17) = _
 have numeric : (((18446744073709551615 : BitVec 64) * (0 : BitVec 64))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_0_11_0
example (s : riscv_state) : «dfn'MUL» (0,1,1) (fixture s 0 9223372036854775809 18446744073709551615) = (let t := fixture s 0 9223372036854775809 18446744073709551615; t) := by
 change «write'GPR» (((9223372036854775809 : BitVec 64) * (9223372036854775809 : BitVec 64)), 0) (fixture s 0 9223372036854775809 18446744073709551615) = _
 have numeric : (((9223372036854775809 : BitVec 64) * (9223372036854775809 : BitVec 64))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_0_11_1
example (s : riscv_state) : «dfn'MUL» (1,1,1) (fixture s 0 9223372036854775809 18446744073709551615) = (let t := fixture s 0 9223372036854775809 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((9223372036854775809 : BitVec 64) * (9223372036854775809 : BitVec 64)), 1) (fixture s 0 9223372036854775809 18446744073709551615) = _
 have numeric : (((9223372036854775809 : BitVec 64) * (9223372036854775809 : BitVec 64))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_0_11_2
example (s : riscv_state) : «dfn'MUL» (2,1,1) (fixture s 0 9223372036854775809 18446744073709551615) = (let t := fixture s 0 9223372036854775809 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((9223372036854775809 : BitVec 64) * (9223372036854775809 : BitVec 64)), 2) (fixture s 0 9223372036854775809 18446744073709551615) = _
 have numeric : (((9223372036854775809 : BitVec 64) * (9223372036854775809 : BitVec 64))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_0_11_7
example (s : riscv_state) : «dfn'MUL» (7,1,1) (fixture s 0 9223372036854775809 18446744073709551615) = (let t := fixture s 0 9223372036854775809 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((9223372036854775809 : BitVec 64) * (9223372036854775809 : BitVec 64)), 7) (fixture s 0 9223372036854775809 18446744073709551615) = _
 have numeric : (((9223372036854775809 : BitVec 64) * (9223372036854775809 : BitVec 64))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_2_0_0
example (s : riscv_state) : «dfn'MUL» (0,1,2) (fixture s 2 0 0) = (let t := fixture s 2 0 0; t) := by
 change «write'GPR» (((0 : BitVec 64) * (0 : BitVec 64)), 0) (fixture s 2 0 0) = _
 have numeric : (((0 : BitVec 64) * (0 : BitVec 64))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_2_0_1
example (s : riscv_state) : «dfn'MUL» (1,1,2) (fixture s 2 0 0) = (let t := fixture s 2 0 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((0 : BitVec 64) * (0 : BitVec 64)), 1) (fixture s 2 0 0) = _
 have numeric : (((0 : BitVec 64) * (0 : BitVec 64))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_2_0_2
example (s : riscv_state) : «dfn'MUL» (2,1,2) (fixture s 2 0 0) = (let t := fixture s 2 0 0; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((0 : BitVec 64) * (0 : BitVec 64)), 2) (fixture s 2 0 0) = _
 have numeric : (((0 : BitVec 64) * (0 : BitVec 64))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_2_0_7
example (s : riscv_state) : «dfn'MUL» (7,1,2) (fixture s 2 0 0) = (let t := fixture s 2 0 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((0 : BitVec 64) * (0 : BitVec 64)), 7) (fixture s 2 0 0) = _
 have numeric : (((0 : BitVec 64) * (0 : BitVec 64))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_2_1_0
example (s : riscv_state) : «dfn'MUL» (0,1,2) (fixture s 2 18446744073709551615 18446744073709551615) = (let t := fixture s 2 18446744073709551615 18446744073709551615; t) := by
 change «write'GPR» (((18446744073709551615 : BitVec 64) * (18446744073709551615 : BitVec 64)), 0) (fixture s 2 18446744073709551615 18446744073709551615) = _
 have numeric : (((18446744073709551615 : BitVec 64) * (18446744073709551615 : BitVec 64))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_2_1_1
example (s : riscv_state) : «dfn'MUL» (1,1,2) (fixture s 2 18446744073709551615 18446744073709551615) = (let t := fixture s 2 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((18446744073709551615 : BitVec 64) * (18446744073709551615 : BitVec 64)), 1) (fixture s 2 18446744073709551615 18446744073709551615) = _
 have numeric : (((18446744073709551615 : BitVec 64) * (18446744073709551615 : BitVec 64))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_2_1_2
example (s : riscv_state) : «dfn'MUL» (2,1,2) (fixture s 2 18446744073709551615 18446744073709551615) = (let t := fixture s 2 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((18446744073709551615 : BitVec 64) * (18446744073709551615 : BitVec 64)), 2) (fixture s 2 18446744073709551615 18446744073709551615) = _
 have numeric : (((18446744073709551615 : BitVec 64) * (18446744073709551615 : BitVec 64))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_2_1_7
example (s : riscv_state) : «dfn'MUL» (7,1,2) (fixture s 2 18446744073709551615 18446744073709551615) = (let t := fixture s 2 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((18446744073709551615 : BitVec 64) * (18446744073709551615 : BitVec 64)), 7) (fixture s 2 18446744073709551615 18446744073709551615) = _
 have numeric : (((18446744073709551615 : BitVec 64) * (18446744073709551615 : BitVec 64))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_2_2_0
example (s : riscv_state) : «dfn'MUL» (0,1,2) (fixture s 2 18446744073709551615 2) = (let t := fixture s 2 18446744073709551615 2; t) := by
 change «write'GPR» (((18446744073709551615 : BitVec 64) * (2 : BitVec 64)), 0) (fixture s 2 18446744073709551615 2) = _
 have numeric : (((18446744073709551615 : BitVec 64) * (2 : BitVec 64))) = (18446744073709551614 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_2_2_1
example (s : riscv_state) : «dfn'MUL» (1,1,2) (fixture s 2 18446744073709551615 2) = (let t := fixture s 2 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((18446744073709551615 : BitVec 64) * (2 : BitVec 64)), 1) (fixture s 2 18446744073709551615 2) = _
 have numeric : (((18446744073709551615 : BitVec 64) * (2 : BitVec 64))) = (18446744073709551614 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_2_2_2
example (s : riscv_state) : «dfn'MUL» (2,1,2) (fixture s 2 18446744073709551615 2) = (let t := fixture s 2 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((18446744073709551615 : BitVec 64) * (2 : BitVec 64)), 2) (fixture s 2 18446744073709551615 2) = _
 have numeric : (((18446744073709551615 : BitVec 64) * (2 : BitVec 64))) = (18446744073709551614 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_2_2_7
example (s : riscv_state) : «dfn'MUL» (7,1,2) (fixture s 2 18446744073709551615 2) = (let t := fixture s 2 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((18446744073709551615 : BitVec 64) * (2 : BitVec 64)), 7) (fixture s 2 18446744073709551615 2) = _
 have numeric : (((18446744073709551615 : BitVec 64) * (2 : BitVec 64))) = (18446744073709551614 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_2_3_0
example (s : riscv_state) : «dfn'MUL» (0,1,2) (fixture s 2 2147483648 2147483648) = (let t := fixture s 2 2147483648 2147483648; t) := by
 change «write'GPR» (((2147483648 : BitVec 64) * (2147483648 : BitVec 64)), 0) (fixture s 2 2147483648 2147483648) = _
 have numeric : (((2147483648 : BitVec 64) * (2147483648 : BitVec 64))) = (4611686018427387904 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_2_3_1
example (s : riscv_state) : «dfn'MUL» (1,1,2) (fixture s 2 2147483648 2147483648) = (let t := fixture s 2 2147483648 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 1 4611686018427387904 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((2147483648 : BitVec 64) * (2147483648 : BitVec 64)), 1) (fixture s 2 2147483648 2147483648) = _
 have numeric : (((2147483648 : BitVec 64) * (2147483648 : BitVec 64))) = (4611686018427387904 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_2_3_2
example (s : riscv_state) : «dfn'MUL» (2,1,2) (fixture s 2 2147483648 2147483648) = (let t := fixture s 2 2147483648 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 2 4611686018427387904 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((2147483648 : BitVec 64) * (2147483648 : BitVec 64)), 2) (fixture s 2 2147483648 2147483648) = _
 have numeric : (((2147483648 : BitVec 64) * (2147483648 : BitVec 64))) = (4611686018427387904 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_2_3_7
example (s : riscv_state) : «dfn'MUL» (7,1,2) (fixture s 2 2147483648 2147483648) = (let t := fixture s 2 2147483648 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 7 4611686018427387904 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((2147483648 : BitVec 64) * (2147483648 : BitVec 64)), 7) (fixture s 2 2147483648 2147483648) = _
 have numeric : (((2147483648 : BitVec 64) * (2147483648 : BitVec 64))) = (4611686018427387904 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_2_4_0
example (s : riscv_state) : «dfn'MUL» (0,1,2) (fixture s 2 4294967295 4294967295) = (let t := fixture s 2 4294967295 4294967295; t) := by
 change «write'GPR» (((4294967295 : BitVec 64) * (4294967295 : BitVec 64)), 0) (fixture s 2 4294967295 4294967295) = _
 have numeric : (((4294967295 : BitVec 64) * (4294967295 : BitVec 64))) = (18446744065119617025 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_2_4_1
example (s : riscv_state) : «dfn'MUL» (1,1,2) (fixture s 2 4294967295 4294967295) = (let t := fixture s 2 4294967295 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744065119617025 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((4294967295 : BitVec 64) * (4294967295 : BitVec 64)), 1) (fixture s 2 4294967295 4294967295) = _
 have numeric : (((4294967295 : BitVec 64) * (4294967295 : BitVec 64))) = (18446744065119617025 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_2_4_2
example (s : riscv_state) : «dfn'MUL» (2,1,2) (fixture s 2 4294967295 4294967295) = (let t := fixture s 2 4294967295 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744065119617025 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((4294967295 : BitVec 64) * (4294967295 : BitVec 64)), 2) (fixture s 2 4294967295 4294967295) = _
 have numeric : (((4294967295 : BitVec 64) * (4294967295 : BitVec 64))) = (18446744065119617025 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_2_4_7
example (s : riscv_state) : «dfn'MUL» (7,1,2) (fixture s 2 4294967295 4294967295) = (let t := fixture s 2 4294967295 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744065119617025 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((4294967295 : BitVec 64) * (4294967295 : BitVec 64)), 7) (fixture s 2 4294967295 4294967295) = _
 have numeric : (((4294967295 : BitVec 64) * (4294967295 : BitVec 64))) = (18446744065119617025 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_2_5_0
example (s : riscv_state) : «dfn'MUL» (0,1,2) (fixture s 2 9223372036854775808 2) = (let t := fixture s 2 9223372036854775808 2; t) := by
 change «write'GPR» (((9223372036854775808 : BitVec 64) * (2 : BitVec 64)), 0) (fixture s 2 9223372036854775808 2) = _
 have numeric : (((9223372036854775808 : BitVec 64) * (2 : BitVec 64))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_2_5_1
example (s : riscv_state) : «dfn'MUL» (1,1,2) (fixture s 2 9223372036854775808 2) = (let t := fixture s 2 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((9223372036854775808 : BitVec 64) * (2 : BitVec 64)), 1) (fixture s 2 9223372036854775808 2) = _
 have numeric : (((9223372036854775808 : BitVec 64) * (2 : BitVec 64))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_2_5_2
example (s : riscv_state) : «dfn'MUL» (2,1,2) (fixture s 2 9223372036854775808 2) = (let t := fixture s 2 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((9223372036854775808 : BitVec 64) * (2 : BitVec 64)), 2) (fixture s 2 9223372036854775808 2) = _
 have numeric : (((9223372036854775808 : BitVec 64) * (2 : BitVec 64))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_2_5_7
example (s : riscv_state) : «dfn'MUL» (7,1,2) (fixture s 2 9223372036854775808 2) = (let t := fixture s 2 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((9223372036854775808 : BitVec 64) * (2 : BitVec 64)), 7) (fixture s 2 9223372036854775808 2) = _
 have numeric : (((9223372036854775808 : BitVec 64) * (2 : BitVec 64))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_2_6_0
example (s : riscv_state) : «dfn'MUL» (0,1,2) (fixture s 2 9223372036854775808 18446744073709551615) = (let t := fixture s 2 9223372036854775808 18446744073709551615; t) := by
 change «write'GPR» (((9223372036854775808 : BitVec 64) * (18446744073709551615 : BitVec 64)), 0) (fixture s 2 9223372036854775808 18446744073709551615) = _
 have numeric : (((9223372036854775808 : BitVec 64) * (18446744073709551615 : BitVec 64))) = (9223372036854775808 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_2_6_1
example (s : riscv_state) : «dfn'MUL» (1,1,2) (fixture s 2 9223372036854775808 18446744073709551615) = (let t := fixture s 2 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((9223372036854775808 : BitVec 64) * (18446744073709551615 : BitVec 64)), 1) (fixture s 2 9223372036854775808 18446744073709551615) = _
 have numeric : (((9223372036854775808 : BitVec 64) * (18446744073709551615 : BitVec 64))) = (9223372036854775808 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_2_6_2
example (s : riscv_state) : «dfn'MUL» (2,1,2) (fixture s 2 9223372036854775808 18446744073709551615) = (let t := fixture s 2 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((9223372036854775808 : BitVec 64) * (18446744073709551615 : BitVec 64)), 2) (fixture s 2 9223372036854775808 18446744073709551615) = _
 have numeric : (((9223372036854775808 : BitVec 64) * (18446744073709551615 : BitVec 64))) = (9223372036854775808 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_2_6_7
example (s : riscv_state) : «dfn'MUL» (7,1,2) (fixture s 2 9223372036854775808 18446744073709551615) = (let t := fixture s 2 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((9223372036854775808 : BitVec 64) * (18446744073709551615 : BitVec 64)), 7) (fixture s 2 9223372036854775808 18446744073709551615) = _
 have numeric : (((9223372036854775808 : BitVec 64) * (18446744073709551615 : BitVec 64))) = (9223372036854775808 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_2_7_0
example (s : riscv_state) : «dfn'MUL» (0,1,2) (fixture s 2 9223372036854775807 9223372036854775807) = (let t := fixture s 2 9223372036854775807 9223372036854775807; t) := by
 change «write'GPR» (((9223372036854775807 : BitVec 64) * (9223372036854775807 : BitVec 64)), 0) (fixture s 2 9223372036854775807 9223372036854775807) = _
 have numeric : (((9223372036854775807 : BitVec 64) * (9223372036854775807 : BitVec 64))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_2_7_1
example (s : riscv_state) : «dfn'MUL» (1,1,2) (fixture s 2 9223372036854775807 9223372036854775807) = (let t := fixture s 2 9223372036854775807 9223372036854775807; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((9223372036854775807 : BitVec 64) * (9223372036854775807 : BitVec 64)), 1) (fixture s 2 9223372036854775807 9223372036854775807) = _
 have numeric : (((9223372036854775807 : BitVec 64) * (9223372036854775807 : BitVec 64))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_2_7_2
example (s : riscv_state) : «dfn'MUL» (2,1,2) (fixture s 2 9223372036854775807 9223372036854775807) = (let t := fixture s 2 9223372036854775807 9223372036854775807; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((9223372036854775807 : BitVec 64) * (9223372036854775807 : BitVec 64)), 2) (fixture s 2 9223372036854775807 9223372036854775807) = _
 have numeric : (((9223372036854775807 : BitVec 64) * (9223372036854775807 : BitVec 64))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_2_7_7
example (s : riscv_state) : «dfn'MUL» (7,1,2) (fixture s 2 9223372036854775807 9223372036854775807) = (let t := fixture s 2 9223372036854775807 9223372036854775807; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((9223372036854775807 : BitVec 64) * (9223372036854775807 : BitVec 64)), 7) (fixture s 2 9223372036854775807 9223372036854775807) = _
 have numeric : (((9223372036854775807 : BitVec 64) * (9223372036854775807 : BitVec 64))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_2_8_0
example (s : riscv_state) : «dfn'MUL» (0,1,2) (fixture s 2 4294967297 4294967297) = (let t := fixture s 2 4294967297 4294967297; t) := by
 change «write'GPR» (((4294967297 : BitVec 64) * (4294967297 : BitVec 64)), 0) (fixture s 2 4294967297 4294967297) = _
 have numeric : (((4294967297 : BitVec 64) * (4294967297 : BitVec 64))) = (8589934593 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_2_8_1
example (s : riscv_state) : «dfn'MUL» (1,1,2) (fixture s 2 4294967297 4294967297) = (let t := fixture s 2 4294967297 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 1 8589934593 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((4294967297 : BitVec 64) * (4294967297 : BitVec 64)), 1) (fixture s 2 4294967297 4294967297) = _
 have numeric : (((4294967297 : BitVec 64) * (4294967297 : BitVec 64))) = (8589934593 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_2_8_2
example (s : riscv_state) : «dfn'MUL» (2,1,2) (fixture s 2 4294967297 4294967297) = (let t := fixture s 2 4294967297 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 2 8589934593 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((4294967297 : BitVec 64) * (4294967297 : BitVec 64)), 2) (fixture s 2 4294967297 4294967297) = _
 have numeric : (((4294967297 : BitVec 64) * (4294967297 : BitVec 64))) = (8589934593 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_2_8_7
example (s : riscv_state) : «dfn'MUL» (7,1,2) (fixture s 2 4294967297 4294967297) = (let t := fixture s 2 4294967297 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 7 8589934593 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((4294967297 : BitVec 64) * (4294967297 : BitVec 64)), 7) (fixture s 2 4294967297 4294967297) = _
 have numeric : (((4294967297 : BitVec 64) * (4294967297 : BitVec 64))) = (8589934593 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_2_9_0
example (s : riscv_state) : «dfn'MUL» (0,0,2) (fixture s 2 17 18446744073709551615) = (let t := fixture s 2 17 18446744073709551615; t) := by
 change «write'GPR» (((0 : BitVec 64) * (18446744073709551615 : BitVec 64)), 0) (fixture s 2 17 18446744073709551615) = _
 have numeric : (((0 : BitVec 64) * (18446744073709551615 : BitVec 64))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_2_9_1
example (s : riscv_state) : «dfn'MUL» (1,0,2) (fixture s 2 17 18446744073709551615) = (let t := fixture s 2 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((0 : BitVec 64) * (18446744073709551615 : BitVec 64)), 1) (fixture s 2 17 18446744073709551615) = _
 have numeric : (((0 : BitVec 64) * (18446744073709551615 : BitVec 64))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_2_9_2
example (s : riscv_state) : «dfn'MUL» (2,0,2) (fixture s 2 17 18446744073709551615) = (let t := fixture s 2 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((0 : BitVec 64) * (18446744073709551615 : BitVec 64)), 2) (fixture s 2 17 18446744073709551615) = _
 have numeric : (((0 : BitVec 64) * (18446744073709551615 : BitVec 64))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_2_9_7
example (s : riscv_state) : «dfn'MUL» (7,0,2) (fixture s 2 17 18446744073709551615) = (let t := fixture s 2 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((0 : BitVec 64) * (18446744073709551615 : BitVec 64)), 7) (fixture s 2 17 18446744073709551615) = _
 have numeric : (((0 : BitVec 64) * (18446744073709551615 : BitVec 64))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_2_10_0
example (s : riscv_state) : «dfn'MUL» (0,1,0) (fixture s 2 18446744073709551615 17) = (let t := fixture s 2 18446744073709551615 17; t) := by
 change «write'GPR» (((18446744073709551615 : BitVec 64) * (0 : BitVec 64)), 0) (fixture s 2 18446744073709551615 17) = _
 have numeric : (((18446744073709551615 : BitVec 64) * (0 : BitVec 64))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_2_10_1
example (s : riscv_state) : «dfn'MUL» (1,1,0) (fixture s 2 18446744073709551615 17) = (let t := fixture s 2 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((18446744073709551615 : BitVec 64) * (0 : BitVec 64)), 1) (fixture s 2 18446744073709551615 17) = _
 have numeric : (((18446744073709551615 : BitVec 64) * (0 : BitVec 64))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_2_10_2
example (s : riscv_state) : «dfn'MUL» (2,1,0) (fixture s 2 18446744073709551615 17) = (let t := fixture s 2 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((18446744073709551615 : BitVec 64) * (0 : BitVec 64)), 2) (fixture s 2 18446744073709551615 17) = _
 have numeric : (((18446744073709551615 : BitVec 64) * (0 : BitVec 64))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_2_10_7
example (s : riscv_state) : «dfn'MUL» (7,1,0) (fixture s 2 18446744073709551615 17) = (let t := fixture s 2 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((18446744073709551615 : BitVec 64) * (0 : BitVec 64)), 7) (fixture s 2 18446744073709551615 17) = _
 have numeric : (((18446744073709551615 : BitVec 64) * (0 : BitVec 64))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_2_11_0
example (s : riscv_state) : «dfn'MUL» (0,1,1) (fixture s 2 9223372036854775809 18446744073709551615) = (let t := fixture s 2 9223372036854775809 18446744073709551615; t) := by
 change «write'GPR» (((9223372036854775809 : BitVec 64) * (9223372036854775809 : BitVec 64)), 0) (fixture s 2 9223372036854775809 18446744073709551615) = _
 have numeric : (((9223372036854775809 : BitVec 64) * (9223372036854775809 : BitVec 64))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_2_11_1
example (s : riscv_state) : «dfn'MUL» (1,1,1) (fixture s 2 9223372036854775809 18446744073709551615) = (let t := fixture s 2 9223372036854775809 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((9223372036854775809 : BitVec 64) * (9223372036854775809 : BitVec 64)), 1) (fixture s 2 9223372036854775809 18446744073709551615) = _
 have numeric : (((9223372036854775809 : BitVec 64) * (9223372036854775809 : BitVec 64))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_2_11_2
example (s : riscv_state) : «dfn'MUL» (2,1,1) (fixture s 2 9223372036854775809 18446744073709551615) = (let t := fixture s 2 9223372036854775809 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((9223372036854775809 : BitVec 64) * (9223372036854775809 : BitVec 64)), 2) (fixture s 2 9223372036854775809 18446744073709551615) = _
 have numeric : (((9223372036854775809 : BitVec 64) * (9223372036854775809 : BitVec 64))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_2_11_7
example (s : riscv_state) : «dfn'MUL» (7,1,1) (fixture s 2 9223372036854775809 18446744073709551615) = (let t := fixture s 2 9223372036854775809 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((9223372036854775809 : BitVec 64) * (9223372036854775809 : BitVec 64)), 7) (fixture s 2 9223372036854775809 18446744073709551615) = _
 have numeric : (((9223372036854775809 : BitVec 64) * (9223372036854775809 : BitVec 64))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_3_0_0
example (s : riscv_state) : «dfn'MUL» (0,1,2) (fixture s 3 0 0) = (let t := fixture s 3 0 0; t) := by
 change «write'GPR» (((0 : BitVec 64) * (0 : BitVec 64)), 0) (fixture s 3 0 0) = _
 have numeric : (((0 : BitVec 64) * (0 : BitVec 64))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_3_0_1
example (s : riscv_state) : «dfn'MUL» (1,1,2) (fixture s 3 0 0) = (let t := fixture s 3 0 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((0 : BitVec 64) * (0 : BitVec 64)), 1) (fixture s 3 0 0) = _
 have numeric : (((0 : BitVec 64) * (0 : BitVec 64))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_3_0_2
example (s : riscv_state) : «dfn'MUL» (2,1,2) (fixture s 3 0 0) = (let t := fixture s 3 0 0; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((0 : BitVec 64) * (0 : BitVec 64)), 2) (fixture s 3 0 0) = _
 have numeric : (((0 : BitVec 64) * (0 : BitVec 64))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_3_0_7
example (s : riscv_state) : «dfn'MUL» (7,1,2) (fixture s 3 0 0) = (let t := fixture s 3 0 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((0 : BitVec 64) * (0 : BitVec 64)), 7) (fixture s 3 0 0) = _
 have numeric : (((0 : BitVec 64) * (0 : BitVec 64))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_3_1_0
example (s : riscv_state) : «dfn'MUL» (0,1,2) (fixture s 3 18446744073709551615 18446744073709551615) = (let t := fixture s 3 18446744073709551615 18446744073709551615; t) := by
 change «write'GPR» (((18446744073709551615 : BitVec 64) * (18446744073709551615 : BitVec 64)), 0) (fixture s 3 18446744073709551615 18446744073709551615) = _
 have numeric : (((18446744073709551615 : BitVec 64) * (18446744073709551615 : BitVec 64))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_3_1_1
example (s : riscv_state) : «dfn'MUL» (1,1,2) (fixture s 3 18446744073709551615 18446744073709551615) = (let t := fixture s 3 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((18446744073709551615 : BitVec 64) * (18446744073709551615 : BitVec 64)), 1) (fixture s 3 18446744073709551615 18446744073709551615) = _
 have numeric : (((18446744073709551615 : BitVec 64) * (18446744073709551615 : BitVec 64))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_3_1_2
example (s : riscv_state) : «dfn'MUL» (2,1,2) (fixture s 3 18446744073709551615 18446744073709551615) = (let t := fixture s 3 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((18446744073709551615 : BitVec 64) * (18446744073709551615 : BitVec 64)), 2) (fixture s 3 18446744073709551615 18446744073709551615) = _
 have numeric : (((18446744073709551615 : BitVec 64) * (18446744073709551615 : BitVec 64))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_3_1_7
example (s : riscv_state) : «dfn'MUL» (7,1,2) (fixture s 3 18446744073709551615 18446744073709551615) = (let t := fixture s 3 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((18446744073709551615 : BitVec 64) * (18446744073709551615 : BitVec 64)), 7) (fixture s 3 18446744073709551615 18446744073709551615) = _
 have numeric : (((18446744073709551615 : BitVec 64) * (18446744073709551615 : BitVec 64))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_3_2_0
example (s : riscv_state) : «dfn'MUL» (0,1,2) (fixture s 3 18446744073709551615 2) = (let t := fixture s 3 18446744073709551615 2; t) := by
 change «write'GPR» (((18446744073709551615 : BitVec 64) * (2 : BitVec 64)), 0) (fixture s 3 18446744073709551615 2) = _
 have numeric : (((18446744073709551615 : BitVec 64) * (2 : BitVec 64))) = (18446744073709551614 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_3_2_1
example (s : riscv_state) : «dfn'MUL» (1,1,2) (fixture s 3 18446744073709551615 2) = (let t := fixture s 3 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((18446744073709551615 : BitVec 64) * (2 : BitVec 64)), 1) (fixture s 3 18446744073709551615 2) = _
 have numeric : (((18446744073709551615 : BitVec 64) * (2 : BitVec 64))) = (18446744073709551614 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_3_2_2
example (s : riscv_state) : «dfn'MUL» (2,1,2) (fixture s 3 18446744073709551615 2) = (let t := fixture s 3 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((18446744073709551615 : BitVec 64) * (2 : BitVec 64)), 2) (fixture s 3 18446744073709551615 2) = _
 have numeric : (((18446744073709551615 : BitVec 64) * (2 : BitVec 64))) = (18446744073709551614 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_3_2_7
example (s : riscv_state) : «dfn'MUL» (7,1,2) (fixture s 3 18446744073709551615 2) = (let t := fixture s 3 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((18446744073709551615 : BitVec 64) * (2 : BitVec 64)), 7) (fixture s 3 18446744073709551615 2) = _
 have numeric : (((18446744073709551615 : BitVec 64) * (2 : BitVec 64))) = (18446744073709551614 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_3_3_0
example (s : riscv_state) : «dfn'MUL» (0,1,2) (fixture s 3 2147483648 2147483648) = (let t := fixture s 3 2147483648 2147483648; t) := by
 change «write'GPR» (((2147483648 : BitVec 64) * (2147483648 : BitVec 64)), 0) (fixture s 3 2147483648 2147483648) = _
 have numeric : (((2147483648 : BitVec 64) * (2147483648 : BitVec 64))) = (4611686018427387904 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_3_3_1
example (s : riscv_state) : «dfn'MUL» (1,1,2) (fixture s 3 2147483648 2147483648) = (let t := fixture s 3 2147483648 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 1 4611686018427387904 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((2147483648 : BitVec 64) * (2147483648 : BitVec 64)), 1) (fixture s 3 2147483648 2147483648) = _
 have numeric : (((2147483648 : BitVec 64) * (2147483648 : BitVec 64))) = (4611686018427387904 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_3_3_2
example (s : riscv_state) : «dfn'MUL» (2,1,2) (fixture s 3 2147483648 2147483648) = (let t := fixture s 3 2147483648 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 2 4611686018427387904 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((2147483648 : BitVec 64) * (2147483648 : BitVec 64)), 2) (fixture s 3 2147483648 2147483648) = _
 have numeric : (((2147483648 : BitVec 64) * (2147483648 : BitVec 64))) = (4611686018427387904 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_3_3_7
example (s : riscv_state) : «dfn'MUL» (7,1,2) (fixture s 3 2147483648 2147483648) = (let t := fixture s 3 2147483648 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 7 4611686018427387904 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((2147483648 : BitVec 64) * (2147483648 : BitVec 64)), 7) (fixture s 3 2147483648 2147483648) = _
 have numeric : (((2147483648 : BitVec 64) * (2147483648 : BitVec 64))) = (4611686018427387904 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_3_4_0
example (s : riscv_state) : «dfn'MUL» (0,1,2) (fixture s 3 4294967295 4294967295) = (let t := fixture s 3 4294967295 4294967295; t) := by
 change «write'GPR» (((4294967295 : BitVec 64) * (4294967295 : BitVec 64)), 0) (fixture s 3 4294967295 4294967295) = _
 have numeric : (((4294967295 : BitVec 64) * (4294967295 : BitVec 64))) = (18446744065119617025 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_3_4_1
example (s : riscv_state) : «dfn'MUL» (1,1,2) (fixture s 3 4294967295 4294967295) = (let t := fixture s 3 4294967295 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744065119617025 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((4294967295 : BitVec 64) * (4294967295 : BitVec 64)), 1) (fixture s 3 4294967295 4294967295) = _
 have numeric : (((4294967295 : BitVec 64) * (4294967295 : BitVec 64))) = (18446744065119617025 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_3_4_2
example (s : riscv_state) : «dfn'MUL» (2,1,2) (fixture s 3 4294967295 4294967295) = (let t := fixture s 3 4294967295 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744065119617025 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((4294967295 : BitVec 64) * (4294967295 : BitVec 64)), 2) (fixture s 3 4294967295 4294967295) = _
 have numeric : (((4294967295 : BitVec 64) * (4294967295 : BitVec 64))) = (18446744065119617025 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_3_4_7
example (s : riscv_state) : «dfn'MUL» (7,1,2) (fixture s 3 4294967295 4294967295) = (let t := fixture s 3 4294967295 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744065119617025 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((4294967295 : BitVec 64) * (4294967295 : BitVec 64)), 7) (fixture s 3 4294967295 4294967295) = _
 have numeric : (((4294967295 : BitVec 64) * (4294967295 : BitVec 64))) = (18446744065119617025 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_3_5_0
example (s : riscv_state) : «dfn'MUL» (0,1,2) (fixture s 3 9223372036854775808 2) = (let t := fixture s 3 9223372036854775808 2; t) := by
 change «write'GPR» (((9223372036854775808 : BitVec 64) * (2 : BitVec 64)), 0) (fixture s 3 9223372036854775808 2) = _
 have numeric : (((9223372036854775808 : BitVec 64) * (2 : BitVec 64))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_3_5_1
example (s : riscv_state) : «dfn'MUL» (1,1,2) (fixture s 3 9223372036854775808 2) = (let t := fixture s 3 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((9223372036854775808 : BitVec 64) * (2 : BitVec 64)), 1) (fixture s 3 9223372036854775808 2) = _
 have numeric : (((9223372036854775808 : BitVec 64) * (2 : BitVec 64))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_3_5_2
example (s : riscv_state) : «dfn'MUL» (2,1,2) (fixture s 3 9223372036854775808 2) = (let t := fixture s 3 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((9223372036854775808 : BitVec 64) * (2 : BitVec 64)), 2) (fixture s 3 9223372036854775808 2) = _
 have numeric : (((9223372036854775808 : BitVec 64) * (2 : BitVec 64))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_3_5_7
example (s : riscv_state) : «dfn'MUL» (7,1,2) (fixture s 3 9223372036854775808 2) = (let t := fixture s 3 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((9223372036854775808 : BitVec 64) * (2 : BitVec 64)), 7) (fixture s 3 9223372036854775808 2) = _
 have numeric : (((9223372036854775808 : BitVec 64) * (2 : BitVec 64))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_3_6_0
example (s : riscv_state) : «dfn'MUL» (0,1,2) (fixture s 3 9223372036854775808 18446744073709551615) = (let t := fixture s 3 9223372036854775808 18446744073709551615; t) := by
 change «write'GPR» (((9223372036854775808 : BitVec 64) * (18446744073709551615 : BitVec 64)), 0) (fixture s 3 9223372036854775808 18446744073709551615) = _
 have numeric : (((9223372036854775808 : BitVec 64) * (18446744073709551615 : BitVec 64))) = (9223372036854775808 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_3_6_1
example (s : riscv_state) : «dfn'MUL» (1,1,2) (fixture s 3 9223372036854775808 18446744073709551615) = (let t := fixture s 3 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((9223372036854775808 : BitVec 64) * (18446744073709551615 : BitVec 64)), 1) (fixture s 3 9223372036854775808 18446744073709551615) = _
 have numeric : (((9223372036854775808 : BitVec 64) * (18446744073709551615 : BitVec 64))) = (9223372036854775808 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_3_6_2
example (s : riscv_state) : «dfn'MUL» (2,1,2) (fixture s 3 9223372036854775808 18446744073709551615) = (let t := fixture s 3 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((9223372036854775808 : BitVec 64) * (18446744073709551615 : BitVec 64)), 2) (fixture s 3 9223372036854775808 18446744073709551615) = _
 have numeric : (((9223372036854775808 : BitVec 64) * (18446744073709551615 : BitVec 64))) = (9223372036854775808 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_3_6_7
example (s : riscv_state) : «dfn'MUL» (7,1,2) (fixture s 3 9223372036854775808 18446744073709551615) = (let t := fixture s 3 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((9223372036854775808 : BitVec 64) * (18446744073709551615 : BitVec 64)), 7) (fixture s 3 9223372036854775808 18446744073709551615) = _
 have numeric : (((9223372036854775808 : BitVec 64) * (18446744073709551615 : BitVec 64))) = (9223372036854775808 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_3_7_0
example (s : riscv_state) : «dfn'MUL» (0,1,2) (fixture s 3 9223372036854775807 9223372036854775807) = (let t := fixture s 3 9223372036854775807 9223372036854775807; t) := by
 change «write'GPR» (((9223372036854775807 : BitVec 64) * (9223372036854775807 : BitVec 64)), 0) (fixture s 3 9223372036854775807 9223372036854775807) = _
 have numeric : (((9223372036854775807 : BitVec 64) * (9223372036854775807 : BitVec 64))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_3_7_1
example (s : riscv_state) : «dfn'MUL» (1,1,2) (fixture s 3 9223372036854775807 9223372036854775807) = (let t := fixture s 3 9223372036854775807 9223372036854775807; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((9223372036854775807 : BitVec 64) * (9223372036854775807 : BitVec 64)), 1) (fixture s 3 9223372036854775807 9223372036854775807) = _
 have numeric : (((9223372036854775807 : BitVec 64) * (9223372036854775807 : BitVec 64))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_3_7_2
example (s : riscv_state) : «dfn'MUL» (2,1,2) (fixture s 3 9223372036854775807 9223372036854775807) = (let t := fixture s 3 9223372036854775807 9223372036854775807; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((9223372036854775807 : BitVec 64) * (9223372036854775807 : BitVec 64)), 2) (fixture s 3 9223372036854775807 9223372036854775807) = _
 have numeric : (((9223372036854775807 : BitVec 64) * (9223372036854775807 : BitVec 64))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_3_7_7
example (s : riscv_state) : «dfn'MUL» (7,1,2) (fixture s 3 9223372036854775807 9223372036854775807) = (let t := fixture s 3 9223372036854775807 9223372036854775807; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((9223372036854775807 : BitVec 64) * (9223372036854775807 : BitVec 64)), 7) (fixture s 3 9223372036854775807 9223372036854775807) = _
 have numeric : (((9223372036854775807 : BitVec 64) * (9223372036854775807 : BitVec 64))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_3_8_0
example (s : riscv_state) : «dfn'MUL» (0,1,2) (fixture s 3 4294967297 4294967297) = (let t := fixture s 3 4294967297 4294967297; t) := by
 change «write'GPR» (((4294967297 : BitVec 64) * (4294967297 : BitVec 64)), 0) (fixture s 3 4294967297 4294967297) = _
 have numeric : (((4294967297 : BitVec 64) * (4294967297 : BitVec 64))) = (8589934593 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_3_8_1
example (s : riscv_state) : «dfn'MUL» (1,1,2) (fixture s 3 4294967297 4294967297) = (let t := fixture s 3 4294967297 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 1 8589934593 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((4294967297 : BitVec 64) * (4294967297 : BitVec 64)), 1) (fixture s 3 4294967297 4294967297) = _
 have numeric : (((4294967297 : BitVec 64) * (4294967297 : BitVec 64))) = (8589934593 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_3_8_2
example (s : riscv_state) : «dfn'MUL» (2,1,2) (fixture s 3 4294967297 4294967297) = (let t := fixture s 3 4294967297 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 2 8589934593 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((4294967297 : BitVec 64) * (4294967297 : BitVec 64)), 2) (fixture s 3 4294967297 4294967297) = _
 have numeric : (((4294967297 : BitVec 64) * (4294967297 : BitVec 64))) = (8589934593 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_3_8_7
example (s : riscv_state) : «dfn'MUL» (7,1,2) (fixture s 3 4294967297 4294967297) = (let t := fixture s 3 4294967297 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 7 8589934593 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((4294967297 : BitVec 64) * (4294967297 : BitVec 64)), 7) (fixture s 3 4294967297 4294967297) = _
 have numeric : (((4294967297 : BitVec 64) * (4294967297 : BitVec 64))) = (8589934593 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_3_9_0
example (s : riscv_state) : «dfn'MUL» (0,0,2) (fixture s 3 17 18446744073709551615) = (let t := fixture s 3 17 18446744073709551615; t) := by
 change «write'GPR» (((0 : BitVec 64) * (18446744073709551615 : BitVec 64)), 0) (fixture s 3 17 18446744073709551615) = _
 have numeric : (((0 : BitVec 64) * (18446744073709551615 : BitVec 64))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_3_9_1
example (s : riscv_state) : «dfn'MUL» (1,0,2) (fixture s 3 17 18446744073709551615) = (let t := fixture s 3 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((0 : BitVec 64) * (18446744073709551615 : BitVec 64)), 1) (fixture s 3 17 18446744073709551615) = _
 have numeric : (((0 : BitVec 64) * (18446744073709551615 : BitVec 64))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_3_9_2
example (s : riscv_state) : «dfn'MUL» (2,0,2) (fixture s 3 17 18446744073709551615) = (let t := fixture s 3 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((0 : BitVec 64) * (18446744073709551615 : BitVec 64)), 2) (fixture s 3 17 18446744073709551615) = _
 have numeric : (((0 : BitVec 64) * (18446744073709551615 : BitVec 64))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_3_9_7
example (s : riscv_state) : «dfn'MUL» (7,0,2) (fixture s 3 17 18446744073709551615) = (let t := fixture s 3 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((0 : BitVec 64) * (18446744073709551615 : BitVec 64)), 7) (fixture s 3 17 18446744073709551615) = _
 have numeric : (((0 : BitVec 64) * (18446744073709551615 : BitVec 64))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_3_10_0
example (s : riscv_state) : «dfn'MUL» (0,1,0) (fixture s 3 18446744073709551615 17) = (let t := fixture s 3 18446744073709551615 17; t) := by
 change «write'GPR» (((18446744073709551615 : BitVec 64) * (0 : BitVec 64)), 0) (fixture s 3 18446744073709551615 17) = _
 have numeric : (((18446744073709551615 : BitVec 64) * (0 : BitVec 64))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_3_10_1
example (s : riscv_state) : «dfn'MUL» (1,1,0) (fixture s 3 18446744073709551615 17) = (let t := fixture s 3 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((18446744073709551615 : BitVec 64) * (0 : BitVec 64)), 1) (fixture s 3 18446744073709551615 17) = _
 have numeric : (((18446744073709551615 : BitVec 64) * (0 : BitVec 64))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_3_10_2
example (s : riscv_state) : «dfn'MUL» (2,1,0) (fixture s 3 18446744073709551615 17) = (let t := fixture s 3 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((18446744073709551615 : BitVec 64) * (0 : BitVec 64)), 2) (fixture s 3 18446744073709551615 17) = _
 have numeric : (((18446744073709551615 : BitVec 64) * (0 : BitVec 64))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_3_10_7
example (s : riscv_state) : «dfn'MUL» (7,1,0) (fixture s 3 18446744073709551615 17) = (let t := fixture s 3 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((18446744073709551615 : BitVec 64) * (0 : BitVec 64)), 7) (fixture s 3 18446744073709551615 17) = _
 have numeric : (((18446744073709551615 : BitVec 64) * (0 : BitVec 64))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_3_11_0
example (s : riscv_state) : «dfn'MUL» (0,1,1) (fixture s 3 9223372036854775809 18446744073709551615) = (let t := fixture s 3 9223372036854775809 18446744073709551615; t) := by
 change «write'GPR» (((9223372036854775809 : BitVec 64) * (9223372036854775809 : BitVec 64)), 0) (fixture s 3 9223372036854775809 18446744073709551615) = _
 have numeric : (((9223372036854775809 : BitVec 64) * (9223372036854775809 : BitVec 64))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_3_11_1
example (s : riscv_state) : «dfn'MUL» (1,1,1) (fixture s 3 9223372036854775809 18446744073709551615) = (let t := fixture s 3 9223372036854775809 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((9223372036854775809 : BitVec 64) * (9223372036854775809 : BitVec 64)), 1) (fixture s 3 9223372036854775809 18446744073709551615) = _
 have numeric : (((9223372036854775809 : BitVec 64) * (9223372036854775809 : BitVec 64))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_3_11_2
example (s : riscv_state) : «dfn'MUL» (2,1,1) (fixture s 3 9223372036854775809 18446744073709551615) = (let t := fixture s 3 9223372036854775809 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((9223372036854775809 : BitVec 64) * (9223372036854775809 : BitVec 64)), 2) (fixture s 3 9223372036854775809 18446744073709551615) = _
 have numeric : (((9223372036854775809 : BitVec 64) * (9223372036854775809 : BitVec 64))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MUL_3_11_7
example (s : riscv_state) : «dfn'MUL» (7,1,1) (fixture s 3 9223372036854775809 18446744073709551615) = (let t := fixture s 3 9223372036854775809 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (((9223372036854775809 : BitVec 64) * (9223372036854775809 : BitVec 64)), 7) (fixture s 3 9223372036854775809 18446744073709551615) = _
 have numeric : (((9223372036854775809 : BitVec 64) * (9223372036854775809 : BitVec 64))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_0_0_0
example (s : riscv_state) : «dfn'MULH» (0,1,2) (fixture s 0 0 0) = (let t := fixture s 0 0 0; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))))), 0) (fixture s 0 0 0) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_0_0_1
example (s : riscv_state) : «dfn'MULH» (1,1,2) (fixture s 0 0 0) = (let t := fixture s 0 0 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))))), 1) (fixture s 0 0 0) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_0_0_2
example (s : riscv_state) : «dfn'MULH» (2,1,2) (fixture s 0 0 0) = (let t := fixture s 0 0 0; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))))), 2) (fixture s 0 0 0) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_0_0_7
example (s : riscv_state) : «dfn'MULH» (7,1,2) (fixture s 0 0 0) = (let t := fixture s 0 0 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))))), 7) (fixture s 0 0 0) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_0_1_0
example (s : riscv_state) : «dfn'MULH» (0,1,2) (fixture s 0 18446744073709551615 18446744073709551615) = (let t := fixture s 0 18446744073709551615 18446744073709551615; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))))), 0) (fixture s 0 18446744073709551615 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_0_1_1
example (s : riscv_state) : «dfn'MULH» (1,1,2) (fixture s 0 18446744073709551615 18446744073709551615) = (let t := fixture s 0 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))))), 1) (fixture s 0 18446744073709551615 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_0_1_2
example (s : riscv_state) : «dfn'MULH» (2,1,2) (fixture s 0 18446744073709551615 18446744073709551615) = (let t := fixture s 0 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))))), 2) (fixture s 0 18446744073709551615 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_0_1_7
example (s : riscv_state) : «dfn'MULH» (7,1,2) (fixture s 0 18446744073709551615 18446744073709551615) = (let t := fixture s 0 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))))), 7) (fixture s 0 18446744073709551615 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_0_2_0
example (s : riscv_state) : «dfn'MULH» (0,1,2) (fixture s 0 18446744073709551615 2) = (let t := fixture s 0 18446744073709551615 2; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (2 : BitVec 64)))))), 0) (fixture s 0 18446744073709551615 2) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (2 : BitVec 64))))))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_0_2_1
example (s : riscv_state) : «dfn'MULH» (1,1,2) (fixture s 0 18446744073709551615 2) = (let t := fixture s 0 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (2 : BitVec 64)))))), 1) (fixture s 0 18446744073709551615 2) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (2 : BitVec 64))))))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_0_2_2
example (s : riscv_state) : «dfn'MULH» (2,1,2) (fixture s 0 18446744073709551615 2) = (let t := fixture s 0 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (2 : BitVec 64)))))), 2) (fixture s 0 18446744073709551615 2) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (2 : BitVec 64))))))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_0_2_7
example (s : riscv_state) : «dfn'MULH» (7,1,2) (fixture s 0 18446744073709551615 2) = (let t := fixture s 0 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (2 : BitVec 64)))))), 7) (fixture s 0 18446744073709551615 2) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (2 : BitVec 64))))))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_0_3_0
example (s : riscv_state) : «dfn'MULH» (0,1,2) (fixture s 0 2147483648 2147483648) = (let t := fixture s 0 2147483648 2147483648; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64)))))), 0) (fixture s 0 2147483648 2147483648) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))))))) = (1073741824 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_0_3_1
example (s : riscv_state) : «dfn'MULH» (1,1,2) (fixture s 0 2147483648 2147483648) = (let t := fixture s 0 2147483648 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 1 1073741824 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64)))))), 1) (fixture s 0 2147483648 2147483648) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))))))) = (1073741824 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_0_3_2
example (s : riscv_state) : «dfn'MULH» (2,1,2) (fixture s 0 2147483648 2147483648) = (let t := fixture s 0 2147483648 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 2 1073741824 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64)))))), 2) (fixture s 0 2147483648 2147483648) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))))))) = (1073741824 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_0_3_7
example (s : riscv_state) : «dfn'MULH» (7,1,2) (fixture s 0 2147483648 2147483648) = (let t := fixture s 0 2147483648 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 7 1073741824 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64)))))), 7) (fixture s 0 2147483648 2147483648) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))))))) = (1073741824 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_0_4_0
example (s : riscv_state) : «dfn'MULH» (0,1,2) (fixture s 0 4294967295 4294967295) = (let t := fixture s 0 4294967295 4294967295; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967295 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967295 : BitVec 64)))))), 0) (fixture s 0 4294967295 4294967295) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967295 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967295 : BitVec 64))))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_0_4_1
example (s : riscv_state) : «dfn'MULH» (1,1,2) (fixture s 0 4294967295 4294967295) = (let t := fixture s 0 4294967295 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967295 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967295 : BitVec 64)))))), 1) (fixture s 0 4294967295 4294967295) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967295 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967295 : BitVec 64))))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_0_4_2
example (s : riscv_state) : «dfn'MULH» (2,1,2) (fixture s 0 4294967295 4294967295) = (let t := fixture s 0 4294967295 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967295 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967295 : BitVec 64)))))), 2) (fixture s 0 4294967295 4294967295) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967295 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967295 : BitVec 64))))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_0_4_7
example (s : riscv_state) : «dfn'MULH» (7,1,2) (fixture s 0 4294967295 4294967295) = (let t := fixture s 0 4294967295 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967295 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967295 : BitVec 64)))))), 7) (fixture s 0 4294967295 4294967295) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967295 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967295 : BitVec 64))))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_0_5_0
example (s : riscv_state) : «dfn'MULH» (0,1,2) (fixture s 0 9223372036854775808 2) = (let t := fixture s 0 9223372036854775808 2; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (2 : BitVec 64)))))), 0) (fixture s 0 9223372036854775808 2) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (2 : BitVec 64))))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_0_5_1
example (s : riscv_state) : «dfn'MULH» (1,1,2) (fixture s 0 9223372036854775808 2) = (let t := fixture s 0 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (2 : BitVec 64)))))), 1) (fixture s 0 9223372036854775808 2) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (2 : BitVec 64))))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_0_5_2
example (s : riscv_state) : «dfn'MULH» (2,1,2) (fixture s 0 9223372036854775808 2) = (let t := fixture s 0 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (2 : BitVec 64)))))), 2) (fixture s 0 9223372036854775808 2) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (2 : BitVec 64))))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_0_5_7
example (s : riscv_state) : «dfn'MULH» (7,1,2) (fixture s 0 9223372036854775808 2) = (let t := fixture s 0 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (2 : BitVec 64)))))), 7) (fixture s 0 9223372036854775808 2) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (2 : BitVec 64))))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_0_6_0
example (s : riscv_state) : «dfn'MULH» (0,1,2) (fixture s 0 9223372036854775808 18446744073709551615) = (let t := fixture s 0 9223372036854775808 18446744073709551615; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))))), 0) (fixture s 0 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_0_6_1
example (s : riscv_state) : «dfn'MULH» (1,1,2) (fixture s 0 9223372036854775808 18446744073709551615) = (let t := fixture s 0 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))))), 1) (fixture s 0 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_0_6_2
example (s : riscv_state) : «dfn'MULH» (2,1,2) (fixture s 0 9223372036854775808 18446744073709551615) = (let t := fixture s 0 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))))), 2) (fixture s 0 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_0_6_7
example (s : riscv_state) : «dfn'MULH» (7,1,2) (fixture s 0 9223372036854775808 18446744073709551615) = (let t := fixture s 0 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))))), 7) (fixture s 0 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_0_7_0
example (s : riscv_state) : «dfn'MULH» (0,1,2) (fixture s 0 9223372036854775807 9223372036854775807) = (let t := fixture s 0 9223372036854775807 9223372036854775807; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775807 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775807 : BitVec 64)))))), 0) (fixture s 0 9223372036854775807 9223372036854775807) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775807 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775807 : BitVec 64))))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_0_7_1
example (s : riscv_state) : «dfn'MULH» (1,1,2) (fixture s 0 9223372036854775807 9223372036854775807) = (let t := fixture s 0 9223372036854775807 9223372036854775807; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775807 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775807 : BitVec 64)))))), 1) (fixture s 0 9223372036854775807 9223372036854775807) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775807 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775807 : BitVec 64))))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_0_7_2
example (s : riscv_state) : «dfn'MULH» (2,1,2) (fixture s 0 9223372036854775807 9223372036854775807) = (let t := fixture s 0 9223372036854775807 9223372036854775807; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775807 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775807 : BitVec 64)))))), 2) (fixture s 0 9223372036854775807 9223372036854775807) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775807 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775807 : BitVec 64))))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_0_7_7
example (s : riscv_state) : «dfn'MULH» (7,1,2) (fixture s 0 9223372036854775807 9223372036854775807) = (let t := fixture s 0 9223372036854775807 9223372036854775807; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775807 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775807 : BitVec 64)))))), 7) (fixture s 0 9223372036854775807 9223372036854775807) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775807 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775807 : BitVec 64))))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_0_8_0
example (s : riscv_state) : «dfn'MULH» (0,1,2) (fixture s 0 4294967297 4294967297) = (let t := fixture s 0 4294967297 4294967297; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64)))))), 0) (fixture s 0 4294967297 4294967297) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_0_8_1
example (s : riscv_state) : «dfn'MULH» (1,1,2) (fixture s 0 4294967297 4294967297) = (let t := fixture s 0 4294967297 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64)))))), 1) (fixture s 0 4294967297 4294967297) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_0_8_2
example (s : riscv_state) : «dfn'MULH» (2,1,2) (fixture s 0 4294967297 4294967297) = (let t := fixture s 0 4294967297 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64)))))), 2) (fixture s 0 4294967297 4294967297) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_0_8_7
example (s : riscv_state) : «dfn'MULH» (7,1,2) (fixture s 0 4294967297 4294967297) = (let t := fixture s 0 4294967297 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64)))))), 7) (fixture s 0 4294967297 4294967297) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_0_9_0
example (s : riscv_state) : «dfn'MULH» (0,0,2) (fixture s 0 17 18446744073709551615) = (let t := fixture s 0 17 18446744073709551615; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))))), 0) (fixture s 0 17 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_0_9_1
example (s : riscv_state) : «dfn'MULH» (1,0,2) (fixture s 0 17 18446744073709551615) = (let t := fixture s 0 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))))), 1) (fixture s 0 17 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_0_9_2
example (s : riscv_state) : «dfn'MULH» (2,0,2) (fixture s 0 17 18446744073709551615) = (let t := fixture s 0 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))))), 2) (fixture s 0 17 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_0_9_7
example (s : riscv_state) : «dfn'MULH» (7,0,2) (fixture s 0 17 18446744073709551615) = (let t := fixture s 0 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))))), 7) (fixture s 0 17 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_0_10_0
example (s : riscv_state) : «dfn'MULH» (0,1,0) (fixture s 0 18446744073709551615 17) = (let t := fixture s 0 18446744073709551615 17; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))))), 0) (fixture s 0 18446744073709551615 17) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_0_10_1
example (s : riscv_state) : «dfn'MULH» (1,1,0) (fixture s 0 18446744073709551615 17) = (let t := fixture s 0 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))))), 1) (fixture s 0 18446744073709551615 17) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_0_10_2
example (s : riscv_state) : «dfn'MULH» (2,1,0) (fixture s 0 18446744073709551615 17) = (let t := fixture s 0 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))))), 2) (fixture s 0 18446744073709551615 17) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_0_10_7
example (s : riscv_state) : «dfn'MULH» (7,1,0) (fixture s 0 18446744073709551615 17) = (let t := fixture s 0 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))))), 7) (fixture s 0 18446744073709551615 17) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_0_11_0
example (s : riscv_state) : «dfn'MULH» (0,1,1) (fixture s 0 9223372036854775809 18446744073709551615) = (let t := fixture s 0 9223372036854775809 18446744073709551615; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)))))), 0) (fixture s 0 9223372036854775809 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64))))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_0_11_1
example (s : riscv_state) : «dfn'MULH» (1,1,1) (fixture s 0 9223372036854775809 18446744073709551615) = (let t := fixture s 0 9223372036854775809 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)))))), 1) (fixture s 0 9223372036854775809 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64))))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_0_11_2
example (s : riscv_state) : «dfn'MULH» (2,1,1) (fixture s 0 9223372036854775809 18446744073709551615) = (let t := fixture s 0 9223372036854775809 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)))))), 2) (fixture s 0 9223372036854775809 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64))))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_0_11_7
example (s : riscv_state) : «dfn'MULH» (7,1,1) (fixture s 0 9223372036854775809 18446744073709551615) = (let t := fixture s 0 9223372036854775809 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)))))), 7) (fixture s 0 9223372036854775809 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)))) * (BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64))))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_2_0_0
example (s : riscv_state) : «dfn'MULH» (0,1,2) (fixture s 2 0 0) = (let t := fixture s 2 0 0; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.signExtend 128 (0 : BitVec 64)))), 0) (fixture s 2 0 0) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.signExtend 128 (0 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_2_0_1
example (s : riscv_state) : «dfn'MULH» (1,1,2) (fixture s 2 0 0) = (let t := fixture s 2 0 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.signExtend 128 (0 : BitVec 64)))), 1) (fixture s 2 0 0) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.signExtend 128 (0 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_2_0_2
example (s : riscv_state) : «dfn'MULH» (2,1,2) (fixture s 2 0 0) = (let t := fixture s 2 0 0; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.signExtend 128 (0 : BitVec 64)))), 2) (fixture s 2 0 0) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.signExtend 128 (0 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_2_0_7
example (s : riscv_state) : «dfn'MULH» (7,1,2) (fixture s 2 0 0) = (let t := fixture s 2 0 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.signExtend 128 (0 : BitVec 64)))), 7) (fixture s 2 0 0) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.signExtend 128 (0 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_2_1_0
example (s : riscv_state) : «dfn'MULH» (0,1,2) (fixture s 2 18446744073709551615 18446744073709551615) = (let t := fixture s 2 18446744073709551615 18446744073709551615; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.signExtend 128 (18446744073709551615 : BitVec 64)))), 0) (fixture s 2 18446744073709551615 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.signExtend 128 (18446744073709551615 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_2_1_1
example (s : riscv_state) : «dfn'MULH» (1,1,2) (fixture s 2 18446744073709551615 18446744073709551615) = (let t := fixture s 2 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.signExtend 128 (18446744073709551615 : BitVec 64)))), 1) (fixture s 2 18446744073709551615 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.signExtend 128 (18446744073709551615 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_2_1_2
example (s : riscv_state) : «dfn'MULH» (2,1,2) (fixture s 2 18446744073709551615 18446744073709551615) = (let t := fixture s 2 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.signExtend 128 (18446744073709551615 : BitVec 64)))), 2) (fixture s 2 18446744073709551615 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.signExtend 128 (18446744073709551615 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_2_1_7
example (s : riscv_state) : «dfn'MULH» (7,1,2) (fixture s 2 18446744073709551615 18446744073709551615) = (let t := fixture s 2 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.signExtend 128 (18446744073709551615 : BitVec 64)))), 7) (fixture s 2 18446744073709551615 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.signExtend 128 (18446744073709551615 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_2_2_0
example (s : riscv_state) : «dfn'MULH» (0,1,2) (fixture s 2 18446744073709551615 2) = (let t := fixture s 2 18446744073709551615 2; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.signExtend 128 (2 : BitVec 64)))), 0) (fixture s 2 18446744073709551615 2) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.signExtend 128 (2 : BitVec 64))))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_2_2_1
example (s : riscv_state) : «dfn'MULH» (1,1,2) (fixture s 2 18446744073709551615 2) = (let t := fixture s 2 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.signExtend 128 (2 : BitVec 64)))), 1) (fixture s 2 18446744073709551615 2) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.signExtend 128 (2 : BitVec 64))))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_2_2_2
example (s : riscv_state) : «dfn'MULH» (2,1,2) (fixture s 2 18446744073709551615 2) = (let t := fixture s 2 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.signExtend 128 (2 : BitVec 64)))), 2) (fixture s 2 18446744073709551615 2) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.signExtend 128 (2 : BitVec 64))))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_2_2_7
example (s : riscv_state) : «dfn'MULH» (7,1,2) (fixture s 2 18446744073709551615 2) = (let t := fixture s 2 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.signExtend 128 (2 : BitVec 64)))), 7) (fixture s 2 18446744073709551615 2) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.signExtend 128 (2 : BitVec 64))))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_2_3_0
example (s : riscv_state) : «dfn'MULH» (0,1,2) (fixture s 2 2147483648 2147483648) = (let t := fixture s 2 2147483648 2147483648; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (2147483648 : BitVec 64)) * (BitVec.signExtend 128 (2147483648 : BitVec 64)))), 0) (fixture s 2 2147483648 2147483648) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (2147483648 : BitVec 64)) * (BitVec.signExtend 128 (2147483648 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_2_3_1
example (s : riscv_state) : «dfn'MULH» (1,1,2) (fixture s 2 2147483648 2147483648) = (let t := fixture s 2 2147483648 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (2147483648 : BitVec 64)) * (BitVec.signExtend 128 (2147483648 : BitVec 64)))), 1) (fixture s 2 2147483648 2147483648) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (2147483648 : BitVec 64)) * (BitVec.signExtend 128 (2147483648 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_2_3_2
example (s : riscv_state) : «dfn'MULH» (2,1,2) (fixture s 2 2147483648 2147483648) = (let t := fixture s 2 2147483648 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (2147483648 : BitVec 64)) * (BitVec.signExtend 128 (2147483648 : BitVec 64)))), 2) (fixture s 2 2147483648 2147483648) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (2147483648 : BitVec 64)) * (BitVec.signExtend 128 (2147483648 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_2_3_7
example (s : riscv_state) : «dfn'MULH» (7,1,2) (fixture s 2 2147483648 2147483648) = (let t := fixture s 2 2147483648 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (2147483648 : BitVec 64)) * (BitVec.signExtend 128 (2147483648 : BitVec 64)))), 7) (fixture s 2 2147483648 2147483648) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (2147483648 : BitVec 64)) * (BitVec.signExtend 128 (2147483648 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_2_4_0
example (s : riscv_state) : «dfn'MULH» (0,1,2) (fixture s 2 4294967295 4294967295) = (let t := fixture s 2 4294967295 4294967295; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967295 : BitVec 64)) * (BitVec.signExtend 128 (4294967295 : BitVec 64)))), 0) (fixture s 2 4294967295 4294967295) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967295 : BitVec 64)) * (BitVec.signExtend 128 (4294967295 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_2_4_1
example (s : riscv_state) : «dfn'MULH» (1,1,2) (fixture s 2 4294967295 4294967295) = (let t := fixture s 2 4294967295 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967295 : BitVec 64)) * (BitVec.signExtend 128 (4294967295 : BitVec 64)))), 1) (fixture s 2 4294967295 4294967295) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967295 : BitVec 64)) * (BitVec.signExtend 128 (4294967295 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_2_4_2
example (s : riscv_state) : «dfn'MULH» (2,1,2) (fixture s 2 4294967295 4294967295) = (let t := fixture s 2 4294967295 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967295 : BitVec 64)) * (BitVec.signExtend 128 (4294967295 : BitVec 64)))), 2) (fixture s 2 4294967295 4294967295) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967295 : BitVec 64)) * (BitVec.signExtend 128 (4294967295 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_2_4_7
example (s : riscv_state) : «dfn'MULH» (7,1,2) (fixture s 2 4294967295 4294967295) = (let t := fixture s 2 4294967295 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967295 : BitVec 64)) * (BitVec.signExtend 128 (4294967295 : BitVec 64)))), 7) (fixture s 2 4294967295 4294967295) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967295 : BitVec 64)) * (BitVec.signExtend 128 (4294967295 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_2_5_0
example (s : riscv_state) : «dfn'MULH» (0,1,2) (fixture s 2 9223372036854775808 2) = (let t := fixture s 2 9223372036854775808 2; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.signExtend 128 (2 : BitVec 64)))), 0) (fixture s 2 9223372036854775808 2) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.signExtend 128 (2 : BitVec 64))))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_2_5_1
example (s : riscv_state) : «dfn'MULH» (1,1,2) (fixture s 2 9223372036854775808 2) = (let t := fixture s 2 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.signExtend 128 (2 : BitVec 64)))), 1) (fixture s 2 9223372036854775808 2) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.signExtend 128 (2 : BitVec 64))))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_2_5_2
example (s : riscv_state) : «dfn'MULH» (2,1,2) (fixture s 2 9223372036854775808 2) = (let t := fixture s 2 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.signExtend 128 (2 : BitVec 64)))), 2) (fixture s 2 9223372036854775808 2) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.signExtend 128 (2 : BitVec 64))))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_2_5_7
example (s : riscv_state) : «dfn'MULH» (7,1,2) (fixture s 2 9223372036854775808 2) = (let t := fixture s 2 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.signExtend 128 (2 : BitVec 64)))), 7) (fixture s 2 9223372036854775808 2) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.signExtend 128 (2 : BitVec 64))))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_2_6_0
example (s : riscv_state) : «dfn'MULH» (0,1,2) (fixture s 2 9223372036854775808 18446744073709551615) = (let t := fixture s 2 9223372036854775808 18446744073709551615; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.signExtend 128 (18446744073709551615 : BitVec 64)))), 0) (fixture s 2 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.signExtend 128 (18446744073709551615 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_2_6_1
example (s : riscv_state) : «dfn'MULH» (1,1,2) (fixture s 2 9223372036854775808 18446744073709551615) = (let t := fixture s 2 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.signExtend 128 (18446744073709551615 : BitVec 64)))), 1) (fixture s 2 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.signExtend 128 (18446744073709551615 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_2_6_2
example (s : riscv_state) : «dfn'MULH» (2,1,2) (fixture s 2 9223372036854775808 18446744073709551615) = (let t := fixture s 2 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.signExtend 128 (18446744073709551615 : BitVec 64)))), 2) (fixture s 2 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.signExtend 128 (18446744073709551615 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_2_6_7
example (s : riscv_state) : «dfn'MULH» (7,1,2) (fixture s 2 9223372036854775808 18446744073709551615) = (let t := fixture s 2 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.signExtend 128 (18446744073709551615 : BitVec 64)))), 7) (fixture s 2 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.signExtend 128 (18446744073709551615 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_2_7_0
example (s : riscv_state) : «dfn'MULH» (0,1,2) (fixture s 2 9223372036854775807 9223372036854775807) = (let t := fixture s 2 9223372036854775807 9223372036854775807; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775807 : BitVec 64)) * (BitVec.signExtend 128 (9223372036854775807 : BitVec 64)))), 0) (fixture s 2 9223372036854775807 9223372036854775807) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775807 : BitVec 64)) * (BitVec.signExtend 128 (9223372036854775807 : BitVec 64))))) = (4611686018427387903 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_2_7_1
example (s : riscv_state) : «dfn'MULH» (1,1,2) (fixture s 2 9223372036854775807 9223372036854775807) = (let t := fixture s 2 9223372036854775807 9223372036854775807; {t with c_gpr := holUpdate 7 (holUpdate 1 4611686018427387903 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775807 : BitVec 64)) * (BitVec.signExtend 128 (9223372036854775807 : BitVec 64)))), 1) (fixture s 2 9223372036854775807 9223372036854775807) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775807 : BitVec 64)) * (BitVec.signExtend 128 (9223372036854775807 : BitVec 64))))) = (4611686018427387903 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_2_7_2
example (s : riscv_state) : «dfn'MULH» (2,1,2) (fixture s 2 9223372036854775807 9223372036854775807) = (let t := fixture s 2 9223372036854775807 9223372036854775807; {t with c_gpr := holUpdate 7 (holUpdate 2 4611686018427387903 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775807 : BitVec 64)) * (BitVec.signExtend 128 (9223372036854775807 : BitVec 64)))), 2) (fixture s 2 9223372036854775807 9223372036854775807) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775807 : BitVec 64)) * (BitVec.signExtend 128 (9223372036854775807 : BitVec 64))))) = (4611686018427387903 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_2_7_7
example (s : riscv_state) : «dfn'MULH» (7,1,2) (fixture s 2 9223372036854775807 9223372036854775807) = (let t := fixture s 2 9223372036854775807 9223372036854775807; {t with c_gpr := holUpdate 7 (holUpdate 7 4611686018427387903 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775807 : BitVec 64)) * (BitVec.signExtend 128 (9223372036854775807 : BitVec 64)))), 7) (fixture s 2 9223372036854775807 9223372036854775807) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775807 : BitVec 64)) * (BitVec.signExtend 128 (9223372036854775807 : BitVec 64))))) = (4611686018427387903 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_2_8_0
example (s : riscv_state) : «dfn'MULH» (0,1,2) (fixture s 2 4294967297 4294967297) = (let t := fixture s 2 4294967297 4294967297; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967297 : BitVec 64)) * (BitVec.signExtend 128 (4294967297 : BitVec 64)))), 0) (fixture s 2 4294967297 4294967297) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967297 : BitVec 64)) * (BitVec.signExtend 128 (4294967297 : BitVec 64))))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_2_8_1
example (s : riscv_state) : «dfn'MULH» (1,1,2) (fixture s 2 4294967297 4294967297) = (let t := fixture s 2 4294967297 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967297 : BitVec 64)) * (BitVec.signExtend 128 (4294967297 : BitVec 64)))), 1) (fixture s 2 4294967297 4294967297) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967297 : BitVec 64)) * (BitVec.signExtend 128 (4294967297 : BitVec 64))))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_2_8_2
example (s : riscv_state) : «dfn'MULH» (2,1,2) (fixture s 2 4294967297 4294967297) = (let t := fixture s 2 4294967297 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967297 : BitVec 64)) * (BitVec.signExtend 128 (4294967297 : BitVec 64)))), 2) (fixture s 2 4294967297 4294967297) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967297 : BitVec 64)) * (BitVec.signExtend 128 (4294967297 : BitVec 64))))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_2_8_7
example (s : riscv_state) : «dfn'MULH» (7,1,2) (fixture s 2 4294967297 4294967297) = (let t := fixture s 2 4294967297 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967297 : BitVec 64)) * (BitVec.signExtend 128 (4294967297 : BitVec 64)))), 7) (fixture s 2 4294967297 4294967297) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967297 : BitVec 64)) * (BitVec.signExtend 128 (4294967297 : BitVec 64))))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_2_9_0
example (s : riscv_state) : «dfn'MULH» (0,0,2) (fixture s 2 17 18446744073709551615) = (let t := fixture s 2 17 18446744073709551615; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.signExtend 128 (18446744073709551615 : BitVec 64)))), 0) (fixture s 2 17 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.signExtend 128 (18446744073709551615 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_2_9_1
example (s : riscv_state) : «dfn'MULH» (1,0,2) (fixture s 2 17 18446744073709551615) = (let t := fixture s 2 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.signExtend 128 (18446744073709551615 : BitVec 64)))), 1) (fixture s 2 17 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.signExtend 128 (18446744073709551615 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_2_9_2
example (s : riscv_state) : «dfn'MULH» (2,0,2) (fixture s 2 17 18446744073709551615) = (let t := fixture s 2 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.signExtend 128 (18446744073709551615 : BitVec 64)))), 2) (fixture s 2 17 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.signExtend 128 (18446744073709551615 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_2_9_7
example (s : riscv_state) : «dfn'MULH» (7,0,2) (fixture s 2 17 18446744073709551615) = (let t := fixture s 2 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.signExtend 128 (18446744073709551615 : BitVec 64)))), 7) (fixture s 2 17 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.signExtend 128 (18446744073709551615 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_2_10_0
example (s : riscv_state) : «dfn'MULH» (0,1,0) (fixture s 2 18446744073709551615 17) = (let t := fixture s 2 18446744073709551615 17; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.signExtend 128 (0 : BitVec 64)))), 0) (fixture s 2 18446744073709551615 17) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.signExtend 128 (0 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_2_10_1
example (s : riscv_state) : «dfn'MULH» (1,1,0) (fixture s 2 18446744073709551615 17) = (let t := fixture s 2 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.signExtend 128 (0 : BitVec 64)))), 1) (fixture s 2 18446744073709551615 17) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.signExtend 128 (0 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_2_10_2
example (s : riscv_state) : «dfn'MULH» (2,1,0) (fixture s 2 18446744073709551615 17) = (let t := fixture s 2 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.signExtend 128 (0 : BitVec 64)))), 2) (fixture s 2 18446744073709551615 17) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.signExtend 128 (0 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_2_10_7
example (s : riscv_state) : «dfn'MULH» (7,1,0) (fixture s 2 18446744073709551615 17) = (let t := fixture s 2 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.signExtend 128 (0 : BitVec 64)))), 7) (fixture s 2 18446744073709551615 17) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.signExtend 128 (0 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_2_11_0
example (s : riscv_state) : «dfn'MULH» (0,1,1) (fixture s 2 9223372036854775809 18446744073709551615) = (let t := fixture s 2 9223372036854775809 18446744073709551615; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775809 : BitVec 64)) * (BitVec.signExtend 128 (9223372036854775809 : BitVec 64)))), 0) (fixture s 2 9223372036854775809 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775809 : BitVec 64)) * (BitVec.signExtend 128 (9223372036854775809 : BitVec 64))))) = (4611686018427387903 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_2_11_1
example (s : riscv_state) : «dfn'MULH» (1,1,1) (fixture s 2 9223372036854775809 18446744073709551615) = (let t := fixture s 2 9223372036854775809 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 4611686018427387903 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775809 : BitVec 64)) * (BitVec.signExtend 128 (9223372036854775809 : BitVec 64)))), 1) (fixture s 2 9223372036854775809 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775809 : BitVec 64)) * (BitVec.signExtend 128 (9223372036854775809 : BitVec 64))))) = (4611686018427387903 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_2_11_2
example (s : riscv_state) : «dfn'MULH» (2,1,1) (fixture s 2 9223372036854775809 18446744073709551615) = (let t := fixture s 2 9223372036854775809 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 4611686018427387903 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775809 : BitVec 64)) * (BitVec.signExtend 128 (9223372036854775809 : BitVec 64)))), 2) (fixture s 2 9223372036854775809 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775809 : BitVec 64)) * (BitVec.signExtend 128 (9223372036854775809 : BitVec 64))))) = (4611686018427387903 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_2_11_7
example (s : riscv_state) : «dfn'MULH» (7,1,1) (fixture s 2 9223372036854775809 18446744073709551615) = (let t := fixture s 2 9223372036854775809 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 4611686018427387903 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775809 : BitVec 64)) * (BitVec.signExtend 128 (9223372036854775809 : BitVec 64)))), 7) (fixture s 2 9223372036854775809 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775809 : BitVec 64)) * (BitVec.signExtend 128 (9223372036854775809 : BitVec 64))))) = (4611686018427387903 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_3_0_0
example (s : riscv_state) : «dfn'MULH» (0,1,2) (fixture s 3 0 0) = (let t := fixture s 3 0 0; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.signExtend 128 (0 : BitVec 64)))), 0) (fixture s 3 0 0) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.signExtend 128 (0 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_3_0_1
example (s : riscv_state) : «dfn'MULH» (1,1,2) (fixture s 3 0 0) = (let t := fixture s 3 0 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.signExtend 128 (0 : BitVec 64)))), 1) (fixture s 3 0 0) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.signExtend 128 (0 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_3_0_2
example (s : riscv_state) : «dfn'MULH» (2,1,2) (fixture s 3 0 0) = (let t := fixture s 3 0 0; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.signExtend 128 (0 : BitVec 64)))), 2) (fixture s 3 0 0) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.signExtend 128 (0 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_3_0_7
example (s : riscv_state) : «dfn'MULH» (7,1,2) (fixture s 3 0 0) = (let t := fixture s 3 0 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.signExtend 128 (0 : BitVec 64)))), 7) (fixture s 3 0 0) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.signExtend 128 (0 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_3_1_0
example (s : riscv_state) : «dfn'MULH» (0,1,2) (fixture s 3 18446744073709551615 18446744073709551615) = (let t := fixture s 3 18446744073709551615 18446744073709551615; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.signExtend 128 (18446744073709551615 : BitVec 64)))), 0) (fixture s 3 18446744073709551615 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.signExtend 128 (18446744073709551615 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_3_1_1
example (s : riscv_state) : «dfn'MULH» (1,1,2) (fixture s 3 18446744073709551615 18446744073709551615) = (let t := fixture s 3 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.signExtend 128 (18446744073709551615 : BitVec 64)))), 1) (fixture s 3 18446744073709551615 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.signExtend 128 (18446744073709551615 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_3_1_2
example (s : riscv_state) : «dfn'MULH» (2,1,2) (fixture s 3 18446744073709551615 18446744073709551615) = (let t := fixture s 3 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.signExtend 128 (18446744073709551615 : BitVec 64)))), 2) (fixture s 3 18446744073709551615 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.signExtend 128 (18446744073709551615 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_3_1_7
example (s : riscv_state) : «dfn'MULH» (7,1,2) (fixture s 3 18446744073709551615 18446744073709551615) = (let t := fixture s 3 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.signExtend 128 (18446744073709551615 : BitVec 64)))), 7) (fixture s 3 18446744073709551615 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.signExtend 128 (18446744073709551615 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_3_2_0
example (s : riscv_state) : «dfn'MULH» (0,1,2) (fixture s 3 18446744073709551615 2) = (let t := fixture s 3 18446744073709551615 2; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.signExtend 128 (2 : BitVec 64)))), 0) (fixture s 3 18446744073709551615 2) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.signExtend 128 (2 : BitVec 64))))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_3_2_1
example (s : riscv_state) : «dfn'MULH» (1,1,2) (fixture s 3 18446744073709551615 2) = (let t := fixture s 3 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.signExtend 128 (2 : BitVec 64)))), 1) (fixture s 3 18446744073709551615 2) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.signExtend 128 (2 : BitVec 64))))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_3_2_2
example (s : riscv_state) : «dfn'MULH» (2,1,2) (fixture s 3 18446744073709551615 2) = (let t := fixture s 3 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.signExtend 128 (2 : BitVec 64)))), 2) (fixture s 3 18446744073709551615 2) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.signExtend 128 (2 : BitVec 64))))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_3_2_7
example (s : riscv_state) : «dfn'MULH» (7,1,2) (fixture s 3 18446744073709551615 2) = (let t := fixture s 3 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.signExtend 128 (2 : BitVec 64)))), 7) (fixture s 3 18446744073709551615 2) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.signExtend 128 (2 : BitVec 64))))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_3_3_0
example (s : riscv_state) : «dfn'MULH» (0,1,2) (fixture s 3 2147483648 2147483648) = (let t := fixture s 3 2147483648 2147483648; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (2147483648 : BitVec 64)) * (BitVec.signExtend 128 (2147483648 : BitVec 64)))), 0) (fixture s 3 2147483648 2147483648) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (2147483648 : BitVec 64)) * (BitVec.signExtend 128 (2147483648 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_3_3_1
example (s : riscv_state) : «dfn'MULH» (1,1,2) (fixture s 3 2147483648 2147483648) = (let t := fixture s 3 2147483648 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (2147483648 : BitVec 64)) * (BitVec.signExtend 128 (2147483648 : BitVec 64)))), 1) (fixture s 3 2147483648 2147483648) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (2147483648 : BitVec 64)) * (BitVec.signExtend 128 (2147483648 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_3_3_2
example (s : riscv_state) : «dfn'MULH» (2,1,2) (fixture s 3 2147483648 2147483648) = (let t := fixture s 3 2147483648 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (2147483648 : BitVec 64)) * (BitVec.signExtend 128 (2147483648 : BitVec 64)))), 2) (fixture s 3 2147483648 2147483648) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (2147483648 : BitVec 64)) * (BitVec.signExtend 128 (2147483648 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_3_3_7
example (s : riscv_state) : «dfn'MULH» (7,1,2) (fixture s 3 2147483648 2147483648) = (let t := fixture s 3 2147483648 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (2147483648 : BitVec 64)) * (BitVec.signExtend 128 (2147483648 : BitVec 64)))), 7) (fixture s 3 2147483648 2147483648) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (2147483648 : BitVec 64)) * (BitVec.signExtend 128 (2147483648 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_3_4_0
example (s : riscv_state) : «dfn'MULH» (0,1,2) (fixture s 3 4294967295 4294967295) = (let t := fixture s 3 4294967295 4294967295; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967295 : BitVec 64)) * (BitVec.signExtend 128 (4294967295 : BitVec 64)))), 0) (fixture s 3 4294967295 4294967295) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967295 : BitVec 64)) * (BitVec.signExtend 128 (4294967295 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_3_4_1
example (s : riscv_state) : «dfn'MULH» (1,1,2) (fixture s 3 4294967295 4294967295) = (let t := fixture s 3 4294967295 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967295 : BitVec 64)) * (BitVec.signExtend 128 (4294967295 : BitVec 64)))), 1) (fixture s 3 4294967295 4294967295) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967295 : BitVec 64)) * (BitVec.signExtend 128 (4294967295 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_3_4_2
example (s : riscv_state) : «dfn'MULH» (2,1,2) (fixture s 3 4294967295 4294967295) = (let t := fixture s 3 4294967295 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967295 : BitVec 64)) * (BitVec.signExtend 128 (4294967295 : BitVec 64)))), 2) (fixture s 3 4294967295 4294967295) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967295 : BitVec 64)) * (BitVec.signExtend 128 (4294967295 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_3_4_7
example (s : riscv_state) : «dfn'MULH» (7,1,2) (fixture s 3 4294967295 4294967295) = (let t := fixture s 3 4294967295 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967295 : BitVec 64)) * (BitVec.signExtend 128 (4294967295 : BitVec 64)))), 7) (fixture s 3 4294967295 4294967295) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967295 : BitVec 64)) * (BitVec.signExtend 128 (4294967295 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_3_5_0
example (s : riscv_state) : «dfn'MULH» (0,1,2) (fixture s 3 9223372036854775808 2) = (let t := fixture s 3 9223372036854775808 2; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.signExtend 128 (2 : BitVec 64)))), 0) (fixture s 3 9223372036854775808 2) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.signExtend 128 (2 : BitVec 64))))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_3_5_1
example (s : riscv_state) : «dfn'MULH» (1,1,2) (fixture s 3 9223372036854775808 2) = (let t := fixture s 3 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.signExtend 128 (2 : BitVec 64)))), 1) (fixture s 3 9223372036854775808 2) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.signExtend 128 (2 : BitVec 64))))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_3_5_2
example (s : riscv_state) : «dfn'MULH» (2,1,2) (fixture s 3 9223372036854775808 2) = (let t := fixture s 3 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.signExtend 128 (2 : BitVec 64)))), 2) (fixture s 3 9223372036854775808 2) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.signExtend 128 (2 : BitVec 64))))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_3_5_7
example (s : riscv_state) : «dfn'MULH» (7,1,2) (fixture s 3 9223372036854775808 2) = (let t := fixture s 3 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.signExtend 128 (2 : BitVec 64)))), 7) (fixture s 3 9223372036854775808 2) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.signExtend 128 (2 : BitVec 64))))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_3_6_0
example (s : riscv_state) : «dfn'MULH» (0,1,2) (fixture s 3 9223372036854775808 18446744073709551615) = (let t := fixture s 3 9223372036854775808 18446744073709551615; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.signExtend 128 (18446744073709551615 : BitVec 64)))), 0) (fixture s 3 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.signExtend 128 (18446744073709551615 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_3_6_1
example (s : riscv_state) : «dfn'MULH» (1,1,2) (fixture s 3 9223372036854775808 18446744073709551615) = (let t := fixture s 3 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.signExtend 128 (18446744073709551615 : BitVec 64)))), 1) (fixture s 3 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.signExtend 128 (18446744073709551615 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_3_6_2
example (s : riscv_state) : «dfn'MULH» (2,1,2) (fixture s 3 9223372036854775808 18446744073709551615) = (let t := fixture s 3 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.signExtend 128 (18446744073709551615 : BitVec 64)))), 2) (fixture s 3 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.signExtend 128 (18446744073709551615 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_3_6_7
example (s : riscv_state) : «dfn'MULH» (7,1,2) (fixture s 3 9223372036854775808 18446744073709551615) = (let t := fixture s 3 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.signExtend 128 (18446744073709551615 : BitVec 64)))), 7) (fixture s 3 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.signExtend 128 (18446744073709551615 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_3_7_0
example (s : riscv_state) : «dfn'MULH» (0,1,2) (fixture s 3 9223372036854775807 9223372036854775807) = (let t := fixture s 3 9223372036854775807 9223372036854775807; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775807 : BitVec 64)) * (BitVec.signExtend 128 (9223372036854775807 : BitVec 64)))), 0) (fixture s 3 9223372036854775807 9223372036854775807) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775807 : BitVec 64)) * (BitVec.signExtend 128 (9223372036854775807 : BitVec 64))))) = (4611686018427387903 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_3_7_1
example (s : riscv_state) : «dfn'MULH» (1,1,2) (fixture s 3 9223372036854775807 9223372036854775807) = (let t := fixture s 3 9223372036854775807 9223372036854775807; {t with c_gpr := holUpdate 7 (holUpdate 1 4611686018427387903 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775807 : BitVec 64)) * (BitVec.signExtend 128 (9223372036854775807 : BitVec 64)))), 1) (fixture s 3 9223372036854775807 9223372036854775807) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775807 : BitVec 64)) * (BitVec.signExtend 128 (9223372036854775807 : BitVec 64))))) = (4611686018427387903 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_3_7_2
example (s : riscv_state) : «dfn'MULH» (2,1,2) (fixture s 3 9223372036854775807 9223372036854775807) = (let t := fixture s 3 9223372036854775807 9223372036854775807; {t with c_gpr := holUpdate 7 (holUpdate 2 4611686018427387903 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775807 : BitVec 64)) * (BitVec.signExtend 128 (9223372036854775807 : BitVec 64)))), 2) (fixture s 3 9223372036854775807 9223372036854775807) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775807 : BitVec 64)) * (BitVec.signExtend 128 (9223372036854775807 : BitVec 64))))) = (4611686018427387903 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_3_7_7
example (s : riscv_state) : «dfn'MULH» (7,1,2) (fixture s 3 9223372036854775807 9223372036854775807) = (let t := fixture s 3 9223372036854775807 9223372036854775807; {t with c_gpr := holUpdate 7 (holUpdate 7 4611686018427387903 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775807 : BitVec 64)) * (BitVec.signExtend 128 (9223372036854775807 : BitVec 64)))), 7) (fixture s 3 9223372036854775807 9223372036854775807) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775807 : BitVec 64)) * (BitVec.signExtend 128 (9223372036854775807 : BitVec 64))))) = (4611686018427387903 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_3_8_0
example (s : riscv_state) : «dfn'MULH» (0,1,2) (fixture s 3 4294967297 4294967297) = (let t := fixture s 3 4294967297 4294967297; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967297 : BitVec 64)) * (BitVec.signExtend 128 (4294967297 : BitVec 64)))), 0) (fixture s 3 4294967297 4294967297) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967297 : BitVec 64)) * (BitVec.signExtend 128 (4294967297 : BitVec 64))))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_3_8_1
example (s : riscv_state) : «dfn'MULH» (1,1,2) (fixture s 3 4294967297 4294967297) = (let t := fixture s 3 4294967297 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967297 : BitVec 64)) * (BitVec.signExtend 128 (4294967297 : BitVec 64)))), 1) (fixture s 3 4294967297 4294967297) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967297 : BitVec 64)) * (BitVec.signExtend 128 (4294967297 : BitVec 64))))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_3_8_2
example (s : riscv_state) : «dfn'MULH» (2,1,2) (fixture s 3 4294967297 4294967297) = (let t := fixture s 3 4294967297 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967297 : BitVec 64)) * (BitVec.signExtend 128 (4294967297 : BitVec 64)))), 2) (fixture s 3 4294967297 4294967297) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967297 : BitVec 64)) * (BitVec.signExtend 128 (4294967297 : BitVec 64))))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_3_8_7
example (s : riscv_state) : «dfn'MULH» (7,1,2) (fixture s 3 4294967297 4294967297) = (let t := fixture s 3 4294967297 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967297 : BitVec 64)) * (BitVec.signExtend 128 (4294967297 : BitVec 64)))), 7) (fixture s 3 4294967297 4294967297) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967297 : BitVec 64)) * (BitVec.signExtend 128 (4294967297 : BitVec 64))))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_3_9_0
example (s : riscv_state) : «dfn'MULH» (0,0,2) (fixture s 3 17 18446744073709551615) = (let t := fixture s 3 17 18446744073709551615; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.signExtend 128 (18446744073709551615 : BitVec 64)))), 0) (fixture s 3 17 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.signExtend 128 (18446744073709551615 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_3_9_1
example (s : riscv_state) : «dfn'MULH» (1,0,2) (fixture s 3 17 18446744073709551615) = (let t := fixture s 3 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.signExtend 128 (18446744073709551615 : BitVec 64)))), 1) (fixture s 3 17 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.signExtend 128 (18446744073709551615 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_3_9_2
example (s : riscv_state) : «dfn'MULH» (2,0,2) (fixture s 3 17 18446744073709551615) = (let t := fixture s 3 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.signExtend 128 (18446744073709551615 : BitVec 64)))), 2) (fixture s 3 17 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.signExtend 128 (18446744073709551615 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_3_9_7
example (s : riscv_state) : «dfn'MULH» (7,0,2) (fixture s 3 17 18446744073709551615) = (let t := fixture s 3 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.signExtend 128 (18446744073709551615 : BitVec 64)))), 7) (fixture s 3 17 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.signExtend 128 (18446744073709551615 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_3_10_0
example (s : riscv_state) : «dfn'MULH» (0,1,0) (fixture s 3 18446744073709551615 17) = (let t := fixture s 3 18446744073709551615 17; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.signExtend 128 (0 : BitVec 64)))), 0) (fixture s 3 18446744073709551615 17) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.signExtend 128 (0 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_3_10_1
example (s : riscv_state) : «dfn'MULH» (1,1,0) (fixture s 3 18446744073709551615 17) = (let t := fixture s 3 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.signExtend 128 (0 : BitVec 64)))), 1) (fixture s 3 18446744073709551615 17) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.signExtend 128 (0 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_3_10_2
example (s : riscv_state) : «dfn'MULH» (2,1,0) (fixture s 3 18446744073709551615 17) = (let t := fixture s 3 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.signExtend 128 (0 : BitVec 64)))), 2) (fixture s 3 18446744073709551615 17) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.signExtend 128 (0 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_3_10_7
example (s : riscv_state) : «dfn'MULH» (7,1,0) (fixture s 3 18446744073709551615 17) = (let t := fixture s 3 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.signExtend 128 (0 : BitVec 64)))), 7) (fixture s 3 18446744073709551615 17) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.signExtend 128 (0 : BitVec 64))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_3_11_0
example (s : riscv_state) : «dfn'MULH» (0,1,1) (fixture s 3 9223372036854775809 18446744073709551615) = (let t := fixture s 3 9223372036854775809 18446744073709551615; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775809 : BitVec 64)) * (BitVec.signExtend 128 (9223372036854775809 : BitVec 64)))), 0) (fixture s 3 9223372036854775809 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775809 : BitVec 64)) * (BitVec.signExtend 128 (9223372036854775809 : BitVec 64))))) = (4611686018427387903 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_3_11_1
example (s : riscv_state) : «dfn'MULH» (1,1,1) (fixture s 3 9223372036854775809 18446744073709551615) = (let t := fixture s 3 9223372036854775809 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 4611686018427387903 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775809 : BitVec 64)) * (BitVec.signExtend 128 (9223372036854775809 : BitVec 64)))), 1) (fixture s 3 9223372036854775809 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775809 : BitVec 64)) * (BitVec.signExtend 128 (9223372036854775809 : BitVec 64))))) = (4611686018427387903 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_3_11_2
example (s : riscv_state) : «dfn'MULH» (2,1,1) (fixture s 3 9223372036854775809 18446744073709551615) = (let t := fixture s 3 9223372036854775809 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 4611686018427387903 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775809 : BitVec 64)) * (BitVec.signExtend 128 (9223372036854775809 : BitVec 64)))), 2) (fixture s 3 9223372036854775809 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775809 : BitVec 64)) * (BitVec.signExtend 128 (9223372036854775809 : BitVec 64))))) = (4611686018427387903 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULH_3_11_7
example (s : riscv_state) : «dfn'MULH» (7,1,1) (fixture s 3 9223372036854775809 18446744073709551615) = (let t := fixture s 3 9223372036854775809 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 4611686018427387903 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775809 : BitVec 64)) * (BitVec.signExtend 128 (9223372036854775809 : BitVec 64)))), 7) (fixture s 3 9223372036854775809 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775809 : BitVec 64)) * (BitVec.signExtend 128 (9223372036854775809 : BitVec 64))))) = (4611686018427387903 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_0_0_0
example (s : riscv_state) : «dfn'MULHU» (0,1,2) (fixture s 0 0 0) = (let t := fixture s 0 0 0; t) := by
 change «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (0 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (0 : BitVec 64))))), 0) (fixture s 0 0 0) = _
 have numeric : (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (0 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (0 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_0_0_1
example (s : riscv_state) : «dfn'MULHU» (1,1,2) (fixture s 0 0 0) = (let t := fixture s 0 0 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (0 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (0 : BitVec 64))))), 1) (fixture s 0 0 0) = _
 have numeric : (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (0 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (0 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_0_0_2
example (s : riscv_state) : «dfn'MULHU» (2,1,2) (fixture s 0 0 0) = (let t := fixture s 0 0 0; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (0 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (0 : BitVec 64))))), 2) (fixture s 0 0 0) = _
 have numeric : (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (0 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (0 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_0_0_7
example (s : riscv_state) : «dfn'MULHU» (7,1,2) (fixture s 0 0 0) = (let t := fixture s 0 0 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (0 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (0 : BitVec 64))))), 7) (fixture s 0 0 0) = _
 have numeric : (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (0 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (0 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_0_1_0
example (s : riscv_state) : «dfn'MULHU» (0,1,2) (fixture s 0 18446744073709551615 18446744073709551615) = (let t := fixture s 0 18446744073709551615 18446744073709551615; t) := by
 change «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))))), 0) (fixture s 0 18446744073709551615 18446744073709551615) = _
 have numeric : (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))))) = (4294967294 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_0_1_1
example (s : riscv_state) : «dfn'MULHU» (1,1,2) (fixture s 0 18446744073709551615 18446744073709551615) = (let t := fixture s 0 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 4294967294 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))))), 1) (fixture s 0 18446744073709551615 18446744073709551615) = _
 have numeric : (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))))) = (4294967294 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_0_1_2
example (s : riscv_state) : «dfn'MULHU» (2,1,2) (fixture s 0 18446744073709551615 18446744073709551615) = (let t := fixture s 0 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 4294967294 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))))), 2) (fixture s 0 18446744073709551615 18446744073709551615) = _
 have numeric : (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))))) = (4294967294 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_0_1_7
example (s : riscv_state) : «dfn'MULHU» (7,1,2) (fixture s 0 18446744073709551615 18446744073709551615) = (let t := fixture s 0 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 4294967294 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))))), 7) (fixture s 0 18446744073709551615 18446744073709551615) = _
 have numeric : (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))))) = (4294967294 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_0_2_0
example (s : riscv_state) : «dfn'MULHU» (0,1,2) (fixture s 0 18446744073709551615 2) = (let t := fixture s 0 18446744073709551615 2; t) := by
 change «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (2 : BitVec 64))))), 0) (fixture s 0 18446744073709551615 2) = _
 have numeric : (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (2 : BitVec 64)))))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_0_2_1
example (s : riscv_state) : «dfn'MULHU» (1,1,2) (fixture s 0 18446744073709551615 2) = (let t := fixture s 0 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (2 : BitVec 64))))), 1) (fixture s 0 18446744073709551615 2) = _
 have numeric : (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (2 : BitVec 64)))))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_0_2_2
example (s : riscv_state) : «dfn'MULHU» (2,1,2) (fixture s 0 18446744073709551615 2) = (let t := fixture s 0 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (2 : BitVec 64))))), 2) (fixture s 0 18446744073709551615 2) = _
 have numeric : (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (2 : BitVec 64)))))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_0_2_7
example (s : riscv_state) : «dfn'MULHU» (7,1,2) (fixture s 0 18446744073709551615 2) = (let t := fixture s 0 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (2 : BitVec 64))))), 7) (fixture s 0 18446744073709551615 2) = _
 have numeric : (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (2 : BitVec 64)))))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_0_3_0
example (s : riscv_state) : «dfn'MULHU» (0,1,2) (fixture s 0 2147483648 2147483648) = (let t := fixture s 0 2147483648 2147483648; t) := by
 change «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (2147483648 : BitVec 64))))), 0) (fixture s 0 2147483648 2147483648) = _
 have numeric : (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (2147483648 : BitVec 64)))))) = (1073741824 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_0_3_1
example (s : riscv_state) : «dfn'MULHU» (1,1,2) (fixture s 0 2147483648 2147483648) = (let t := fixture s 0 2147483648 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 1 1073741824 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (2147483648 : BitVec 64))))), 1) (fixture s 0 2147483648 2147483648) = _
 have numeric : (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (2147483648 : BitVec 64)))))) = (1073741824 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_0_3_2
example (s : riscv_state) : «dfn'MULHU» (2,1,2) (fixture s 0 2147483648 2147483648) = (let t := fixture s 0 2147483648 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 2 1073741824 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (2147483648 : BitVec 64))))), 2) (fixture s 0 2147483648 2147483648) = _
 have numeric : (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (2147483648 : BitVec 64)))))) = (1073741824 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_0_3_7
example (s : riscv_state) : «dfn'MULHU» (7,1,2) (fixture s 0 2147483648 2147483648) = (let t := fixture s 0 2147483648 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 7 1073741824 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (2147483648 : BitVec 64))))), 7) (fixture s 0 2147483648 2147483648) = _
 have numeric : (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (2147483648 : BitVec 64)))))) = (1073741824 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_0_4_0
example (s : riscv_state) : «dfn'MULHU» (0,1,2) (fixture s 0 4294967295 4294967295) = (let t := fixture s 0 4294967295 4294967295; t) := by
 change «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (4294967295 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (4294967295 : BitVec 64))))), 0) (fixture s 0 4294967295 4294967295) = _
 have numeric : (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (4294967295 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (4294967295 : BitVec 64)))))) = (4294967294 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_0_4_1
example (s : riscv_state) : «dfn'MULHU» (1,1,2) (fixture s 0 4294967295 4294967295) = (let t := fixture s 0 4294967295 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 1 4294967294 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (4294967295 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (4294967295 : BitVec 64))))), 1) (fixture s 0 4294967295 4294967295) = _
 have numeric : (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (4294967295 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (4294967295 : BitVec 64)))))) = (4294967294 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_0_4_2
example (s : riscv_state) : «dfn'MULHU» (2,1,2) (fixture s 0 4294967295 4294967295) = (let t := fixture s 0 4294967295 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 2 4294967294 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (4294967295 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (4294967295 : BitVec 64))))), 2) (fixture s 0 4294967295 4294967295) = _
 have numeric : (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (4294967295 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (4294967295 : BitVec 64)))))) = (4294967294 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_0_4_7
example (s : riscv_state) : «dfn'MULHU» (7,1,2) (fixture s 0 4294967295 4294967295) = (let t := fixture s 0 4294967295 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 7 4294967294 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (4294967295 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (4294967295 : BitVec 64))))), 7) (fixture s 0 4294967295 4294967295) = _
 have numeric : (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (4294967295 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (4294967295 : BitVec 64)))))) = (4294967294 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_0_5_0
example (s : riscv_state) : «dfn'MULHU» (0,1,2) (fixture s 0 9223372036854775808 2) = (let t := fixture s 0 9223372036854775808 2; t) := by
 change «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (2 : BitVec 64))))), 0) (fixture s 0 9223372036854775808 2) = _
 have numeric : (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (2 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_0_5_1
example (s : riscv_state) : «dfn'MULHU» (1,1,2) (fixture s 0 9223372036854775808 2) = (let t := fixture s 0 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (2 : BitVec 64))))), 1) (fixture s 0 9223372036854775808 2) = _
 have numeric : (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (2 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_0_5_2
example (s : riscv_state) : «dfn'MULHU» (2,1,2) (fixture s 0 9223372036854775808 2) = (let t := fixture s 0 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (2 : BitVec 64))))), 2) (fixture s 0 9223372036854775808 2) = _
 have numeric : (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (2 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_0_5_7
example (s : riscv_state) : «dfn'MULHU» (7,1,2) (fixture s 0 9223372036854775808 2) = (let t := fixture s 0 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (2 : BitVec 64))))), 7) (fixture s 0 9223372036854775808 2) = _
 have numeric : (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (2 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_0_6_0
example (s : riscv_state) : «dfn'MULHU» (0,1,2) (fixture s 0 9223372036854775808 18446744073709551615) = (let t := fixture s 0 9223372036854775808 18446744073709551615; t) := by
 change «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))))), 0) (fixture s 0 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_0_6_1
example (s : riscv_state) : «dfn'MULHU» (1,1,2) (fixture s 0 9223372036854775808 18446744073709551615) = (let t := fixture s 0 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))))), 1) (fixture s 0 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_0_6_2
example (s : riscv_state) : «dfn'MULHU» (2,1,2) (fixture s 0 9223372036854775808 18446744073709551615) = (let t := fixture s 0 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))))), 2) (fixture s 0 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_0_6_7
example (s : riscv_state) : «dfn'MULHU» (7,1,2) (fixture s 0 9223372036854775808 18446744073709551615) = (let t := fixture s 0 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))))), 7) (fixture s 0 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_0_7_0
example (s : riscv_state) : «dfn'MULHU» (0,1,2) (fixture s 0 9223372036854775807 9223372036854775807) = (let t := fixture s 0 9223372036854775807 9223372036854775807; t) := by
 change «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775807 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775807 : BitVec 64))))), 0) (fixture s 0 9223372036854775807 9223372036854775807) = _
 have numeric : (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775807 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775807 : BitVec 64)))))) = (4294967294 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_0_7_1
example (s : riscv_state) : «dfn'MULHU» (1,1,2) (fixture s 0 9223372036854775807 9223372036854775807) = (let t := fixture s 0 9223372036854775807 9223372036854775807; {t with c_gpr := holUpdate 7 (holUpdate 1 4294967294 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775807 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775807 : BitVec 64))))), 1) (fixture s 0 9223372036854775807 9223372036854775807) = _
 have numeric : (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775807 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775807 : BitVec 64)))))) = (4294967294 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_0_7_2
example (s : riscv_state) : «dfn'MULHU» (2,1,2) (fixture s 0 9223372036854775807 9223372036854775807) = (let t := fixture s 0 9223372036854775807 9223372036854775807; {t with c_gpr := holUpdate 7 (holUpdate 2 4294967294 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775807 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775807 : BitVec 64))))), 2) (fixture s 0 9223372036854775807 9223372036854775807) = _
 have numeric : (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775807 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775807 : BitVec 64)))))) = (4294967294 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_0_7_7
example (s : riscv_state) : «dfn'MULHU» (7,1,2) (fixture s 0 9223372036854775807 9223372036854775807) = (let t := fixture s 0 9223372036854775807 9223372036854775807; {t with c_gpr := holUpdate 7 (holUpdate 7 4294967294 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775807 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775807 : BitVec 64))))), 7) (fixture s 0 9223372036854775807 9223372036854775807) = _
 have numeric : (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775807 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775807 : BitVec 64)))))) = (4294967294 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_0_8_0
example (s : riscv_state) : «dfn'MULHU» (0,1,2) (fixture s 0 4294967297 4294967297) = (let t := fixture s 0 4294967297 4294967297; t) := by
 change «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (4294967297 : BitVec 64))))), 0) (fixture s 0 4294967297 4294967297) = _
 have numeric : (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (4294967297 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_0_8_1
example (s : riscv_state) : «dfn'MULHU» (1,1,2) (fixture s 0 4294967297 4294967297) = (let t := fixture s 0 4294967297 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (4294967297 : BitVec 64))))), 1) (fixture s 0 4294967297 4294967297) = _
 have numeric : (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (4294967297 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_0_8_2
example (s : riscv_state) : «dfn'MULHU» (2,1,2) (fixture s 0 4294967297 4294967297) = (let t := fixture s 0 4294967297 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (4294967297 : BitVec 64))))), 2) (fixture s 0 4294967297 4294967297) = _
 have numeric : (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (4294967297 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_0_8_7
example (s : riscv_state) : «dfn'MULHU» (7,1,2) (fixture s 0 4294967297 4294967297) = (let t := fixture s 0 4294967297 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (4294967297 : BitVec 64))))), 7) (fixture s 0 4294967297 4294967297) = _
 have numeric : (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (4294967297 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_0_9_0
example (s : riscv_state) : «dfn'MULHU» (0,0,2) (fixture s 0 17 18446744073709551615) = (let t := fixture s 0 17 18446744073709551615; t) := by
 change «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (0 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))))), 0) (fixture s 0 17 18446744073709551615) = _
 have numeric : (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (0 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_0_9_1
example (s : riscv_state) : «dfn'MULHU» (1,0,2) (fixture s 0 17 18446744073709551615) = (let t := fixture s 0 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (0 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))))), 1) (fixture s 0 17 18446744073709551615) = _
 have numeric : (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (0 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_0_9_2
example (s : riscv_state) : «dfn'MULHU» (2,0,2) (fixture s 0 17 18446744073709551615) = (let t := fixture s 0 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (0 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))))), 2) (fixture s 0 17 18446744073709551615) = _
 have numeric : (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (0 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_0_9_7
example (s : riscv_state) : «dfn'MULHU» (7,0,2) (fixture s 0 17 18446744073709551615) = (let t := fixture s 0 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (0 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))))), 7) (fixture s 0 17 18446744073709551615) = _
 have numeric : (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (0 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_0_10_0
example (s : riscv_state) : «dfn'MULHU» (0,1,0) (fixture s 0 18446744073709551615 17) = (let t := fixture s 0 18446744073709551615 17; t) := by
 change «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (0 : BitVec 64))))), 0) (fixture s 0 18446744073709551615 17) = _
 have numeric : (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (0 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_0_10_1
example (s : riscv_state) : «dfn'MULHU» (1,1,0) (fixture s 0 18446744073709551615 17) = (let t := fixture s 0 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (0 : BitVec 64))))), 1) (fixture s 0 18446744073709551615 17) = _
 have numeric : (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (0 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_0_10_2
example (s : riscv_state) : «dfn'MULHU» (2,1,0) (fixture s 0 18446744073709551615 17) = (let t := fixture s 0 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (0 : BitVec 64))))), 2) (fixture s 0 18446744073709551615 17) = _
 have numeric : (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (0 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_0_10_7
example (s : riscv_state) : «dfn'MULHU» (7,1,0) (fixture s 0 18446744073709551615 17) = (let t := fixture s 0 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (0 : BitVec 64))))), 7) (fixture s 0 18446744073709551615 17) = _
 have numeric : (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (0 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_0_11_0
example (s : riscv_state) : «dfn'MULHU» (0,1,1) (fixture s 0 9223372036854775809 18446744073709551615) = (let t := fixture s 0 9223372036854775809 18446744073709551615; t) := by
 change «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64))))), 0) (fixture s 0 9223372036854775809 18446744073709551615) = _
 have numeric : (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_0_11_1
example (s : riscv_state) : «dfn'MULHU» (1,1,1) (fixture s 0 9223372036854775809 18446744073709551615) = (let t := fixture s 0 9223372036854775809 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64))))), 1) (fixture s 0 9223372036854775809 18446744073709551615) = _
 have numeric : (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_0_11_2
example (s : riscv_state) : «dfn'MULHU» (2,1,1) (fixture s 0 9223372036854775809 18446744073709551615) = (let t := fixture s 0 9223372036854775809 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64))))), 2) (fixture s 0 9223372036854775809 18446744073709551615) = _
 have numeric : (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_0_11_7
example (s : riscv_state) : «dfn'MULHU» (7,1,1) (fixture s 0 9223372036854775809 18446744073709551615) = (let t := fixture s 0 9223372036854775809 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64))))), 7) (fixture s 0 9223372036854775809 18446744073709551615) = _
 have numeric : (BitVec.setWidth 64 (holWordExtract 32 63 32 ((BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_2_0_0
example (s : riscv_state) : «dfn'MULHU» (0,1,2) (fixture s 2 0 0) = (let t := fixture s 2 0 0; t) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64))), 0) (fixture s 2 0 0) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_2_0_1
example (s : riscv_state) : «dfn'MULHU» (1,1,2) (fixture s 2 0 0) = (let t := fixture s 2 0 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64))), 1) (fixture s 2 0 0) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_2_0_2
example (s : riscv_state) : «dfn'MULHU» (2,1,2) (fixture s 2 0 0) = (let t := fixture s 2 0 0; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64))), 2) (fixture s 2 0 0) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_2_0_7
example (s : riscv_state) : «dfn'MULHU» (7,1,2) (fixture s 2 0 0) = (let t := fixture s 2 0 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64))), 7) (fixture s 2 0 0) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_2_1_0
example (s : riscv_state) : «dfn'MULHU» (0,1,2) (fixture s 2 18446744073709551615 18446744073709551615) = (let t := fixture s 2 18446744073709551615 18446744073709551615; t) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64))), 0) (fixture s 2 18446744073709551615 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64)))) = (18446744073709551614 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_2_1_1
example (s : riscv_state) : «dfn'MULHU» (1,1,2) (fixture s 2 18446744073709551615 18446744073709551615) = (let t := fixture s 2 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64))), 1) (fixture s 2 18446744073709551615 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64)))) = (18446744073709551614 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_2_1_2
example (s : riscv_state) : «dfn'MULHU» (2,1,2) (fixture s 2 18446744073709551615 18446744073709551615) = (let t := fixture s 2 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64))), 2) (fixture s 2 18446744073709551615 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64)))) = (18446744073709551614 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_2_1_7
example (s : riscv_state) : «dfn'MULHU» (7,1,2) (fixture s 2 18446744073709551615 18446744073709551615) = (let t := fixture s 2 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64))), 7) (fixture s 2 18446744073709551615 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64)))) = (18446744073709551614 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_2_2_0
example (s : riscv_state) : «dfn'MULHU» (0,1,2) (fixture s 2 18446744073709551615 2) = (let t := fixture s 2 18446744073709551615 2; t) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64))), 0) (fixture s 2 18446744073709551615 2) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64)))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_2_2_1
example (s : riscv_state) : «dfn'MULHU» (1,1,2) (fixture s 2 18446744073709551615 2) = (let t := fixture s 2 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64))), 1) (fixture s 2 18446744073709551615 2) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64)))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_2_2_2
example (s : riscv_state) : «dfn'MULHU» (2,1,2) (fixture s 2 18446744073709551615 2) = (let t := fixture s 2 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64))), 2) (fixture s 2 18446744073709551615 2) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64)))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_2_2_7
example (s : riscv_state) : «dfn'MULHU» (7,1,2) (fixture s 2 18446744073709551615 2) = (let t := fixture s 2 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64))), 7) (fixture s 2 18446744073709551615 2) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64)))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_2_3_0
example (s : riscv_state) : «dfn'MULHU» (0,1,2) (fixture s 2 2147483648 2147483648) = (let t := fixture s 2 2147483648 2147483648; t) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (2147483648 : BitVec 64)) * (BitVec.setWidth 128 (2147483648 : BitVec 64))), 0) (fixture s 2 2147483648 2147483648) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (2147483648 : BitVec 64)) * (BitVec.setWidth 128 (2147483648 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_2_3_1
example (s : riscv_state) : «dfn'MULHU» (1,1,2) (fixture s 2 2147483648 2147483648) = (let t := fixture s 2 2147483648 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (2147483648 : BitVec 64)) * (BitVec.setWidth 128 (2147483648 : BitVec 64))), 1) (fixture s 2 2147483648 2147483648) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (2147483648 : BitVec 64)) * (BitVec.setWidth 128 (2147483648 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_2_3_2
example (s : riscv_state) : «dfn'MULHU» (2,1,2) (fixture s 2 2147483648 2147483648) = (let t := fixture s 2 2147483648 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (2147483648 : BitVec 64)) * (BitVec.setWidth 128 (2147483648 : BitVec 64))), 2) (fixture s 2 2147483648 2147483648) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (2147483648 : BitVec 64)) * (BitVec.setWidth 128 (2147483648 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_2_3_7
example (s : riscv_state) : «dfn'MULHU» (7,1,2) (fixture s 2 2147483648 2147483648) = (let t := fixture s 2 2147483648 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (2147483648 : BitVec 64)) * (BitVec.setWidth 128 (2147483648 : BitVec 64))), 7) (fixture s 2 2147483648 2147483648) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (2147483648 : BitVec 64)) * (BitVec.setWidth 128 (2147483648 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_2_4_0
example (s : riscv_state) : «dfn'MULHU» (0,1,2) (fixture s 2 4294967295 4294967295) = (let t := fixture s 2 4294967295 4294967295; t) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (4294967295 : BitVec 64)) * (BitVec.setWidth 128 (4294967295 : BitVec 64))), 0) (fixture s 2 4294967295 4294967295) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (4294967295 : BitVec 64)) * (BitVec.setWidth 128 (4294967295 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_2_4_1
example (s : riscv_state) : «dfn'MULHU» (1,1,2) (fixture s 2 4294967295 4294967295) = (let t := fixture s 2 4294967295 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (4294967295 : BitVec 64)) * (BitVec.setWidth 128 (4294967295 : BitVec 64))), 1) (fixture s 2 4294967295 4294967295) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (4294967295 : BitVec 64)) * (BitVec.setWidth 128 (4294967295 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_2_4_2
example (s : riscv_state) : «dfn'MULHU» (2,1,2) (fixture s 2 4294967295 4294967295) = (let t := fixture s 2 4294967295 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (4294967295 : BitVec 64)) * (BitVec.setWidth 128 (4294967295 : BitVec 64))), 2) (fixture s 2 4294967295 4294967295) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (4294967295 : BitVec 64)) * (BitVec.setWidth 128 (4294967295 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_2_4_7
example (s : riscv_state) : «dfn'MULHU» (7,1,2) (fixture s 2 4294967295 4294967295) = (let t := fixture s 2 4294967295 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (4294967295 : BitVec 64)) * (BitVec.setWidth 128 (4294967295 : BitVec 64))), 7) (fixture s 2 4294967295 4294967295) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (4294967295 : BitVec 64)) * (BitVec.setWidth 128 (4294967295 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_2_5_0
example (s : riscv_state) : «dfn'MULHU» (0,1,2) (fixture s 2 9223372036854775808 2) = (let t := fixture s 2 9223372036854775808 2; t) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64))), 0) (fixture s 2 9223372036854775808 2) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64)))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_2_5_1
example (s : riscv_state) : «dfn'MULHU» (1,1,2) (fixture s 2 9223372036854775808 2) = (let t := fixture s 2 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64))), 1) (fixture s 2 9223372036854775808 2) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64)))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_2_5_2
example (s : riscv_state) : «dfn'MULHU» (2,1,2) (fixture s 2 9223372036854775808 2) = (let t := fixture s 2 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64))), 2) (fixture s 2 9223372036854775808 2) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64)))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_2_5_7
example (s : riscv_state) : «dfn'MULHU» (7,1,2) (fixture s 2 9223372036854775808 2) = (let t := fixture s 2 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64))), 7) (fixture s 2 9223372036854775808 2) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64)))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_2_6_0
example (s : riscv_state) : «dfn'MULHU» (0,1,2) (fixture s 2 9223372036854775808 18446744073709551615) = (let t := fixture s 2 9223372036854775808 18446744073709551615; t) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64))), 0) (fixture s 2 9223372036854775808 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64)))) = (9223372036854775807 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_2_6_1
example (s : riscv_state) : «dfn'MULHU» (1,1,2) (fixture s 2 9223372036854775808 18446744073709551615) = (let t := fixture s 2 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 9223372036854775807 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64))), 1) (fixture s 2 9223372036854775808 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64)))) = (9223372036854775807 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_2_6_2
example (s : riscv_state) : «dfn'MULHU» (2,1,2) (fixture s 2 9223372036854775808 18446744073709551615) = (let t := fixture s 2 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 9223372036854775807 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64))), 2) (fixture s 2 9223372036854775808 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64)))) = (9223372036854775807 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_2_6_7
example (s : riscv_state) : «dfn'MULHU» (7,1,2) (fixture s 2 9223372036854775808 18446744073709551615) = (let t := fixture s 2 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 9223372036854775807 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64))), 7) (fixture s 2 9223372036854775808 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64)))) = (9223372036854775807 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_2_7_0
example (s : riscv_state) : «dfn'MULHU» (0,1,2) (fixture s 2 9223372036854775807 9223372036854775807) = (let t := fixture s 2 9223372036854775807 9223372036854775807; t) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775807 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775807 : BitVec 64))), 0) (fixture s 2 9223372036854775807 9223372036854775807) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775807 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775807 : BitVec 64)))) = (4611686018427387903 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_2_7_1
example (s : riscv_state) : «dfn'MULHU» (1,1,2) (fixture s 2 9223372036854775807 9223372036854775807) = (let t := fixture s 2 9223372036854775807 9223372036854775807; {t with c_gpr := holUpdate 7 (holUpdate 1 4611686018427387903 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775807 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775807 : BitVec 64))), 1) (fixture s 2 9223372036854775807 9223372036854775807) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775807 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775807 : BitVec 64)))) = (4611686018427387903 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_2_7_2
example (s : riscv_state) : «dfn'MULHU» (2,1,2) (fixture s 2 9223372036854775807 9223372036854775807) = (let t := fixture s 2 9223372036854775807 9223372036854775807; {t with c_gpr := holUpdate 7 (holUpdate 2 4611686018427387903 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775807 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775807 : BitVec 64))), 2) (fixture s 2 9223372036854775807 9223372036854775807) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775807 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775807 : BitVec 64)))) = (4611686018427387903 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_2_7_7
example (s : riscv_state) : «dfn'MULHU» (7,1,2) (fixture s 2 9223372036854775807 9223372036854775807) = (let t := fixture s 2 9223372036854775807 9223372036854775807; {t with c_gpr := holUpdate 7 (holUpdate 7 4611686018427387903 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775807 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775807 : BitVec 64))), 7) (fixture s 2 9223372036854775807 9223372036854775807) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775807 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775807 : BitVec 64)))) = (4611686018427387903 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_2_8_0
example (s : riscv_state) : «dfn'MULHU» (0,1,2) (fixture s 2 4294967297 4294967297) = (let t := fixture s 2 4294967297 4294967297; t) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (4294967297 : BitVec 64)) * (BitVec.setWidth 128 (4294967297 : BitVec 64))), 0) (fixture s 2 4294967297 4294967297) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (4294967297 : BitVec 64)) * (BitVec.setWidth 128 (4294967297 : BitVec 64)))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_2_8_1
example (s : riscv_state) : «dfn'MULHU» (1,1,2) (fixture s 2 4294967297 4294967297) = (let t := fixture s 2 4294967297 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (4294967297 : BitVec 64)) * (BitVec.setWidth 128 (4294967297 : BitVec 64))), 1) (fixture s 2 4294967297 4294967297) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (4294967297 : BitVec 64)) * (BitVec.setWidth 128 (4294967297 : BitVec 64)))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_2_8_2
example (s : riscv_state) : «dfn'MULHU» (2,1,2) (fixture s 2 4294967297 4294967297) = (let t := fixture s 2 4294967297 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (4294967297 : BitVec 64)) * (BitVec.setWidth 128 (4294967297 : BitVec 64))), 2) (fixture s 2 4294967297 4294967297) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (4294967297 : BitVec 64)) * (BitVec.setWidth 128 (4294967297 : BitVec 64)))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_2_8_7
example (s : riscv_state) : «dfn'MULHU» (7,1,2) (fixture s 2 4294967297 4294967297) = (let t := fixture s 2 4294967297 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (4294967297 : BitVec 64)) * (BitVec.setWidth 128 (4294967297 : BitVec 64))), 7) (fixture s 2 4294967297 4294967297) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (4294967297 : BitVec 64)) * (BitVec.setWidth 128 (4294967297 : BitVec 64)))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_2_9_0
example (s : riscv_state) : «dfn'MULHU» (0,0,2) (fixture s 2 17 18446744073709551615) = (let t := fixture s 2 17 18446744073709551615; t) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64))), 0) (fixture s 2 17 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_2_9_1
example (s : riscv_state) : «dfn'MULHU» (1,0,2) (fixture s 2 17 18446744073709551615) = (let t := fixture s 2 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64))), 1) (fixture s 2 17 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_2_9_2
example (s : riscv_state) : «dfn'MULHU» (2,0,2) (fixture s 2 17 18446744073709551615) = (let t := fixture s 2 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64))), 2) (fixture s 2 17 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_2_9_7
example (s : riscv_state) : «dfn'MULHU» (7,0,2) (fixture s 2 17 18446744073709551615) = (let t := fixture s 2 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64))), 7) (fixture s 2 17 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_2_10_0
example (s : riscv_state) : «dfn'MULHU» (0,1,0) (fixture s 2 18446744073709551615 17) = (let t := fixture s 2 18446744073709551615 17; t) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64))), 0) (fixture s 2 18446744073709551615 17) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_2_10_1
example (s : riscv_state) : «dfn'MULHU» (1,1,0) (fixture s 2 18446744073709551615 17) = (let t := fixture s 2 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64))), 1) (fixture s 2 18446744073709551615 17) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_2_10_2
example (s : riscv_state) : «dfn'MULHU» (2,1,0) (fixture s 2 18446744073709551615 17) = (let t := fixture s 2 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64))), 2) (fixture s 2 18446744073709551615 17) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_2_10_7
example (s : riscv_state) : «dfn'MULHU» (7,1,0) (fixture s 2 18446744073709551615 17) = (let t := fixture s 2 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64))), 7) (fixture s 2 18446744073709551615 17) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_2_11_0
example (s : riscv_state) : «dfn'MULHU» (0,1,1) (fixture s 2 9223372036854775809 18446744073709551615) = (let t := fixture s 2 9223372036854775809 18446744073709551615; t) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775809 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775809 : BitVec 64))), 0) (fixture s 2 9223372036854775809 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775809 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775809 : BitVec 64)))) = (4611686018427387905 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_2_11_1
example (s : riscv_state) : «dfn'MULHU» (1,1,1) (fixture s 2 9223372036854775809 18446744073709551615) = (let t := fixture s 2 9223372036854775809 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 4611686018427387905 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775809 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775809 : BitVec 64))), 1) (fixture s 2 9223372036854775809 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775809 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775809 : BitVec 64)))) = (4611686018427387905 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_2_11_2
example (s : riscv_state) : «dfn'MULHU» (2,1,1) (fixture s 2 9223372036854775809 18446744073709551615) = (let t := fixture s 2 9223372036854775809 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 4611686018427387905 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775809 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775809 : BitVec 64))), 2) (fixture s 2 9223372036854775809 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775809 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775809 : BitVec 64)))) = (4611686018427387905 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_2_11_7
example (s : riscv_state) : «dfn'MULHU» (7,1,1) (fixture s 2 9223372036854775809 18446744073709551615) = (let t := fixture s 2 9223372036854775809 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 4611686018427387905 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775809 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775809 : BitVec 64))), 7) (fixture s 2 9223372036854775809 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775809 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775809 : BitVec 64)))) = (4611686018427387905 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_3_0_0
example (s : riscv_state) : «dfn'MULHU» (0,1,2) (fixture s 3 0 0) = (let t := fixture s 3 0 0; t) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64))), 0) (fixture s 3 0 0) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_3_0_1
example (s : riscv_state) : «dfn'MULHU» (1,1,2) (fixture s 3 0 0) = (let t := fixture s 3 0 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64))), 1) (fixture s 3 0 0) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_3_0_2
example (s : riscv_state) : «dfn'MULHU» (2,1,2) (fixture s 3 0 0) = (let t := fixture s 3 0 0; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64))), 2) (fixture s 3 0 0) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_3_0_7
example (s : riscv_state) : «dfn'MULHU» (7,1,2) (fixture s 3 0 0) = (let t := fixture s 3 0 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64))), 7) (fixture s 3 0 0) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_3_1_0
example (s : riscv_state) : «dfn'MULHU» (0,1,2) (fixture s 3 18446744073709551615 18446744073709551615) = (let t := fixture s 3 18446744073709551615 18446744073709551615; t) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64))), 0) (fixture s 3 18446744073709551615 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64)))) = (18446744073709551614 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_3_1_1
example (s : riscv_state) : «dfn'MULHU» (1,1,2) (fixture s 3 18446744073709551615 18446744073709551615) = (let t := fixture s 3 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64))), 1) (fixture s 3 18446744073709551615 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64)))) = (18446744073709551614 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_3_1_2
example (s : riscv_state) : «dfn'MULHU» (2,1,2) (fixture s 3 18446744073709551615 18446744073709551615) = (let t := fixture s 3 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64))), 2) (fixture s 3 18446744073709551615 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64)))) = (18446744073709551614 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_3_1_7
example (s : riscv_state) : «dfn'MULHU» (7,1,2) (fixture s 3 18446744073709551615 18446744073709551615) = (let t := fixture s 3 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64))), 7) (fixture s 3 18446744073709551615 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64)))) = (18446744073709551614 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_3_2_0
example (s : riscv_state) : «dfn'MULHU» (0,1,2) (fixture s 3 18446744073709551615 2) = (let t := fixture s 3 18446744073709551615 2; t) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64))), 0) (fixture s 3 18446744073709551615 2) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64)))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_3_2_1
example (s : riscv_state) : «dfn'MULHU» (1,1,2) (fixture s 3 18446744073709551615 2) = (let t := fixture s 3 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64))), 1) (fixture s 3 18446744073709551615 2) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64)))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_3_2_2
example (s : riscv_state) : «dfn'MULHU» (2,1,2) (fixture s 3 18446744073709551615 2) = (let t := fixture s 3 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64))), 2) (fixture s 3 18446744073709551615 2) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64)))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_3_2_7
example (s : riscv_state) : «dfn'MULHU» (7,1,2) (fixture s 3 18446744073709551615 2) = (let t := fixture s 3 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64))), 7) (fixture s 3 18446744073709551615 2) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64)))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_3_3_0
example (s : riscv_state) : «dfn'MULHU» (0,1,2) (fixture s 3 2147483648 2147483648) = (let t := fixture s 3 2147483648 2147483648; t) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (2147483648 : BitVec 64)) * (BitVec.setWidth 128 (2147483648 : BitVec 64))), 0) (fixture s 3 2147483648 2147483648) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (2147483648 : BitVec 64)) * (BitVec.setWidth 128 (2147483648 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_3_3_1
example (s : riscv_state) : «dfn'MULHU» (1,1,2) (fixture s 3 2147483648 2147483648) = (let t := fixture s 3 2147483648 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (2147483648 : BitVec 64)) * (BitVec.setWidth 128 (2147483648 : BitVec 64))), 1) (fixture s 3 2147483648 2147483648) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (2147483648 : BitVec 64)) * (BitVec.setWidth 128 (2147483648 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_3_3_2
example (s : riscv_state) : «dfn'MULHU» (2,1,2) (fixture s 3 2147483648 2147483648) = (let t := fixture s 3 2147483648 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (2147483648 : BitVec 64)) * (BitVec.setWidth 128 (2147483648 : BitVec 64))), 2) (fixture s 3 2147483648 2147483648) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (2147483648 : BitVec 64)) * (BitVec.setWidth 128 (2147483648 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_3_3_7
example (s : riscv_state) : «dfn'MULHU» (7,1,2) (fixture s 3 2147483648 2147483648) = (let t := fixture s 3 2147483648 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (2147483648 : BitVec 64)) * (BitVec.setWidth 128 (2147483648 : BitVec 64))), 7) (fixture s 3 2147483648 2147483648) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (2147483648 : BitVec 64)) * (BitVec.setWidth 128 (2147483648 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_3_4_0
example (s : riscv_state) : «dfn'MULHU» (0,1,2) (fixture s 3 4294967295 4294967295) = (let t := fixture s 3 4294967295 4294967295; t) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (4294967295 : BitVec 64)) * (BitVec.setWidth 128 (4294967295 : BitVec 64))), 0) (fixture s 3 4294967295 4294967295) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (4294967295 : BitVec 64)) * (BitVec.setWidth 128 (4294967295 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_3_4_1
example (s : riscv_state) : «dfn'MULHU» (1,1,2) (fixture s 3 4294967295 4294967295) = (let t := fixture s 3 4294967295 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (4294967295 : BitVec 64)) * (BitVec.setWidth 128 (4294967295 : BitVec 64))), 1) (fixture s 3 4294967295 4294967295) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (4294967295 : BitVec 64)) * (BitVec.setWidth 128 (4294967295 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_3_4_2
example (s : riscv_state) : «dfn'MULHU» (2,1,2) (fixture s 3 4294967295 4294967295) = (let t := fixture s 3 4294967295 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (4294967295 : BitVec 64)) * (BitVec.setWidth 128 (4294967295 : BitVec 64))), 2) (fixture s 3 4294967295 4294967295) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (4294967295 : BitVec 64)) * (BitVec.setWidth 128 (4294967295 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_3_4_7
example (s : riscv_state) : «dfn'MULHU» (7,1,2) (fixture s 3 4294967295 4294967295) = (let t := fixture s 3 4294967295 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (4294967295 : BitVec 64)) * (BitVec.setWidth 128 (4294967295 : BitVec 64))), 7) (fixture s 3 4294967295 4294967295) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (4294967295 : BitVec 64)) * (BitVec.setWidth 128 (4294967295 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_3_5_0
example (s : riscv_state) : «dfn'MULHU» (0,1,2) (fixture s 3 9223372036854775808 2) = (let t := fixture s 3 9223372036854775808 2; t) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64))), 0) (fixture s 3 9223372036854775808 2) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64)))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_3_5_1
example (s : riscv_state) : «dfn'MULHU» (1,1,2) (fixture s 3 9223372036854775808 2) = (let t := fixture s 3 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64))), 1) (fixture s 3 9223372036854775808 2) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64)))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_3_5_2
example (s : riscv_state) : «dfn'MULHU» (2,1,2) (fixture s 3 9223372036854775808 2) = (let t := fixture s 3 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64))), 2) (fixture s 3 9223372036854775808 2) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64)))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_3_5_7
example (s : riscv_state) : «dfn'MULHU» (7,1,2) (fixture s 3 9223372036854775808 2) = (let t := fixture s 3 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64))), 7) (fixture s 3 9223372036854775808 2) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64)))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_3_6_0
example (s : riscv_state) : «dfn'MULHU» (0,1,2) (fixture s 3 9223372036854775808 18446744073709551615) = (let t := fixture s 3 9223372036854775808 18446744073709551615; t) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64))), 0) (fixture s 3 9223372036854775808 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64)))) = (9223372036854775807 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_3_6_1
example (s : riscv_state) : «dfn'MULHU» (1,1,2) (fixture s 3 9223372036854775808 18446744073709551615) = (let t := fixture s 3 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 9223372036854775807 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64))), 1) (fixture s 3 9223372036854775808 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64)))) = (9223372036854775807 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_3_6_2
example (s : riscv_state) : «dfn'MULHU» (2,1,2) (fixture s 3 9223372036854775808 18446744073709551615) = (let t := fixture s 3 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 9223372036854775807 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64))), 2) (fixture s 3 9223372036854775808 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64)))) = (9223372036854775807 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_3_6_7
example (s : riscv_state) : «dfn'MULHU» (7,1,2) (fixture s 3 9223372036854775808 18446744073709551615) = (let t := fixture s 3 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 9223372036854775807 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64))), 7) (fixture s 3 9223372036854775808 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64)))) = (9223372036854775807 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_3_7_0
example (s : riscv_state) : «dfn'MULHU» (0,1,2) (fixture s 3 9223372036854775807 9223372036854775807) = (let t := fixture s 3 9223372036854775807 9223372036854775807; t) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775807 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775807 : BitVec 64))), 0) (fixture s 3 9223372036854775807 9223372036854775807) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775807 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775807 : BitVec 64)))) = (4611686018427387903 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_3_7_1
example (s : riscv_state) : «dfn'MULHU» (1,1,2) (fixture s 3 9223372036854775807 9223372036854775807) = (let t := fixture s 3 9223372036854775807 9223372036854775807; {t with c_gpr := holUpdate 7 (holUpdate 1 4611686018427387903 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775807 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775807 : BitVec 64))), 1) (fixture s 3 9223372036854775807 9223372036854775807) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775807 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775807 : BitVec 64)))) = (4611686018427387903 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_3_7_2
example (s : riscv_state) : «dfn'MULHU» (2,1,2) (fixture s 3 9223372036854775807 9223372036854775807) = (let t := fixture s 3 9223372036854775807 9223372036854775807; {t with c_gpr := holUpdate 7 (holUpdate 2 4611686018427387903 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775807 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775807 : BitVec 64))), 2) (fixture s 3 9223372036854775807 9223372036854775807) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775807 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775807 : BitVec 64)))) = (4611686018427387903 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_3_7_7
example (s : riscv_state) : «dfn'MULHU» (7,1,2) (fixture s 3 9223372036854775807 9223372036854775807) = (let t := fixture s 3 9223372036854775807 9223372036854775807; {t with c_gpr := holUpdate 7 (holUpdate 7 4611686018427387903 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775807 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775807 : BitVec 64))), 7) (fixture s 3 9223372036854775807 9223372036854775807) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775807 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775807 : BitVec 64)))) = (4611686018427387903 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_3_8_0
example (s : riscv_state) : «dfn'MULHU» (0,1,2) (fixture s 3 4294967297 4294967297) = (let t := fixture s 3 4294967297 4294967297; t) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (4294967297 : BitVec 64)) * (BitVec.setWidth 128 (4294967297 : BitVec 64))), 0) (fixture s 3 4294967297 4294967297) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (4294967297 : BitVec 64)) * (BitVec.setWidth 128 (4294967297 : BitVec 64)))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_3_8_1
example (s : riscv_state) : «dfn'MULHU» (1,1,2) (fixture s 3 4294967297 4294967297) = (let t := fixture s 3 4294967297 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (4294967297 : BitVec 64)) * (BitVec.setWidth 128 (4294967297 : BitVec 64))), 1) (fixture s 3 4294967297 4294967297) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (4294967297 : BitVec 64)) * (BitVec.setWidth 128 (4294967297 : BitVec 64)))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_3_8_2
example (s : riscv_state) : «dfn'MULHU» (2,1,2) (fixture s 3 4294967297 4294967297) = (let t := fixture s 3 4294967297 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (4294967297 : BitVec 64)) * (BitVec.setWidth 128 (4294967297 : BitVec 64))), 2) (fixture s 3 4294967297 4294967297) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (4294967297 : BitVec 64)) * (BitVec.setWidth 128 (4294967297 : BitVec 64)))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_3_8_7
example (s : riscv_state) : «dfn'MULHU» (7,1,2) (fixture s 3 4294967297 4294967297) = (let t := fixture s 3 4294967297 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (4294967297 : BitVec 64)) * (BitVec.setWidth 128 (4294967297 : BitVec 64))), 7) (fixture s 3 4294967297 4294967297) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (4294967297 : BitVec 64)) * (BitVec.setWidth 128 (4294967297 : BitVec 64)))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_3_9_0
example (s : riscv_state) : «dfn'MULHU» (0,0,2) (fixture s 3 17 18446744073709551615) = (let t := fixture s 3 17 18446744073709551615; t) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64))), 0) (fixture s 3 17 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_3_9_1
example (s : riscv_state) : «dfn'MULHU» (1,0,2) (fixture s 3 17 18446744073709551615) = (let t := fixture s 3 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64))), 1) (fixture s 3 17 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_3_9_2
example (s : riscv_state) : «dfn'MULHU» (2,0,2) (fixture s 3 17 18446744073709551615) = (let t := fixture s 3 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64))), 2) (fixture s 3 17 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_3_9_7
example (s : riscv_state) : «dfn'MULHU» (7,0,2) (fixture s 3 17 18446744073709551615) = (let t := fixture s 3 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64))), 7) (fixture s 3 17 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_3_10_0
example (s : riscv_state) : «dfn'MULHU» (0,1,0) (fixture s 3 18446744073709551615 17) = (let t := fixture s 3 18446744073709551615 17; t) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64))), 0) (fixture s 3 18446744073709551615 17) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_3_10_1
example (s : riscv_state) : «dfn'MULHU» (1,1,0) (fixture s 3 18446744073709551615 17) = (let t := fixture s 3 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64))), 1) (fixture s 3 18446744073709551615 17) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_3_10_2
example (s : riscv_state) : «dfn'MULHU» (2,1,0) (fixture s 3 18446744073709551615 17) = (let t := fixture s 3 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64))), 2) (fixture s 3 18446744073709551615 17) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_3_10_7
example (s : riscv_state) : «dfn'MULHU» (7,1,0) (fixture s 3 18446744073709551615 17) = (let t := fixture s 3 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64))), 7) (fixture s 3 18446744073709551615 17) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_3_11_0
example (s : riscv_state) : «dfn'MULHU» (0,1,1) (fixture s 3 9223372036854775809 18446744073709551615) = (let t := fixture s 3 9223372036854775809 18446744073709551615; t) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775809 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775809 : BitVec 64))), 0) (fixture s 3 9223372036854775809 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775809 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775809 : BitVec 64)))) = (4611686018427387905 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_3_11_1
example (s : riscv_state) : «dfn'MULHU» (1,1,1) (fixture s 3 9223372036854775809 18446744073709551615) = (let t := fixture s 3 9223372036854775809 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 4611686018427387905 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775809 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775809 : BitVec 64))), 1) (fixture s 3 9223372036854775809 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775809 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775809 : BitVec 64)))) = (4611686018427387905 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_3_11_2
example (s : riscv_state) : «dfn'MULHU» (2,1,1) (fixture s 3 9223372036854775809 18446744073709551615) = (let t := fixture s 3 9223372036854775809 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 4611686018427387905 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775809 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775809 : BitVec 64))), 2) (fixture s 3 9223372036854775809 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775809 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775809 : BitVec 64)))) = (4611686018427387905 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHU_3_11_7
example (s : riscv_state) : «dfn'MULHU» (7,1,1) (fixture s 3 9223372036854775809 18446744073709551615) = (let t := fixture s 3 9223372036854775809 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 4611686018427387905 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775809 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775809 : BitVec 64))), 7) (fixture s 3 9223372036854775809 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.setWidth 128 (9223372036854775809 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775809 : BitVec 64)))) = (4611686018427387905 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_0_0_0
example (s : riscv_state) : «dfn'MULHSU» (0,1,2) (fixture s 0 0 0) = (let t := fixture s 0 0 0; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (0 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (0 : BitVec 64))))), 0) (fixture s 0 0 0) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (0 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (0 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_0_0_1
example (s : riscv_state) : «dfn'MULHSU» (1,1,2) (fixture s 0 0 0) = (let t := fixture s 0 0 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (0 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (0 : BitVec 64))))), 1) (fixture s 0 0 0) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (0 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (0 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_0_0_2
example (s : riscv_state) : «dfn'MULHSU» (2,1,2) (fixture s 0 0 0) = (let t := fixture s 0 0 0; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (0 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (0 : BitVec 64))))), 2) (fixture s 0 0 0) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (0 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (0 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_0_0_7
example (s : riscv_state) : «dfn'MULHSU» (7,1,2) (fixture s 0 0 0) = (let t := fixture s 0 0 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (0 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (0 : BitVec 64))))), 7) (fixture s 0 0 0) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (0 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (0 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_0_1_0
example (s : riscv_state) : «dfn'MULHSU» (0,1,2) (fixture s 0 18446744073709551615 18446744073709551615) = (let t := fixture s 0 18446744073709551615 18446744073709551615; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))))), 0) (fixture s 0 18446744073709551615 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_0_1_1
example (s : riscv_state) : «dfn'MULHSU» (1,1,2) (fixture s 0 18446744073709551615 18446744073709551615) = (let t := fixture s 0 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))))), 1) (fixture s 0 18446744073709551615 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_0_1_2
example (s : riscv_state) : «dfn'MULHSU» (2,1,2) (fixture s 0 18446744073709551615 18446744073709551615) = (let t := fixture s 0 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))))), 2) (fixture s 0 18446744073709551615 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_0_1_7
example (s : riscv_state) : «dfn'MULHSU» (7,1,2) (fixture s 0 18446744073709551615 18446744073709551615) = (let t := fixture s 0 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))))), 7) (fixture s 0 18446744073709551615 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_0_2_0
example (s : riscv_state) : «dfn'MULHSU» (0,1,2) (fixture s 0 18446744073709551615 2) = (let t := fixture s 0 18446744073709551615 2; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (2 : BitVec 64))))), 0) (fixture s 0 18446744073709551615 2) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (2 : BitVec 64)))))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_0_2_1
example (s : riscv_state) : «dfn'MULHSU» (1,1,2) (fixture s 0 18446744073709551615 2) = (let t := fixture s 0 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (2 : BitVec 64))))), 1) (fixture s 0 18446744073709551615 2) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (2 : BitVec 64)))))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_0_2_2
example (s : riscv_state) : «dfn'MULHSU» (2,1,2) (fixture s 0 18446744073709551615 2) = (let t := fixture s 0 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (2 : BitVec 64))))), 2) (fixture s 0 18446744073709551615 2) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (2 : BitVec 64)))))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_0_2_7
example (s : riscv_state) : «dfn'MULHSU» (7,1,2) (fixture s 0 18446744073709551615 2) = (let t := fixture s 0 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (2 : BitVec 64))))), 7) (fixture s 0 18446744073709551615 2) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (2 : BitVec 64)))))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_0_3_0
example (s : riscv_state) : «dfn'MULHSU» (0,1,2) (fixture s 0 2147483648 2147483648) = (let t := fixture s 0 2147483648 2147483648; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (2147483648 : BitVec 64))))), 0) (fixture s 0 2147483648 2147483648) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (2147483648 : BitVec 64)))))) = (18446744072635809792 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_0_3_1
example (s : riscv_state) : «dfn'MULHSU» (1,1,2) (fixture s 0 2147483648 2147483648) = (let t := fixture s 0 2147483648 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744072635809792 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (2147483648 : BitVec 64))))), 1) (fixture s 0 2147483648 2147483648) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (2147483648 : BitVec 64)))))) = (18446744072635809792 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_0_3_2
example (s : riscv_state) : «dfn'MULHSU» (2,1,2) (fixture s 0 2147483648 2147483648) = (let t := fixture s 0 2147483648 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744072635809792 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (2147483648 : BitVec 64))))), 2) (fixture s 0 2147483648 2147483648) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (2147483648 : BitVec 64)))))) = (18446744072635809792 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_0_3_7
example (s : riscv_state) : «dfn'MULHSU» (7,1,2) (fixture s 0 2147483648 2147483648) = (let t := fixture s 0 2147483648 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744072635809792 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (2147483648 : BitVec 64))))), 7) (fixture s 0 2147483648 2147483648) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (2147483648 : BitVec 64)))))) = (18446744072635809792 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_0_4_0
example (s : riscv_state) : «dfn'MULHSU» (0,1,2) (fixture s 0 4294967295 4294967295) = (let t := fixture s 0 4294967295 4294967295; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (4294967295 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (4294967295 : BitVec 64))))), 0) (fixture s 0 4294967295 4294967295) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (4294967295 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (4294967295 : BitVec 64)))))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_0_4_1
example (s : riscv_state) : «dfn'MULHSU» (1,1,2) (fixture s 0 4294967295 4294967295) = (let t := fixture s 0 4294967295 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (4294967295 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (4294967295 : BitVec 64))))), 1) (fixture s 0 4294967295 4294967295) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (4294967295 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (4294967295 : BitVec 64)))))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_0_4_2
example (s : riscv_state) : «dfn'MULHSU» (2,1,2) (fixture s 0 4294967295 4294967295) = (let t := fixture s 0 4294967295 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (4294967295 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (4294967295 : BitVec 64))))), 2) (fixture s 0 4294967295 4294967295) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (4294967295 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (4294967295 : BitVec 64)))))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_0_4_7
example (s : riscv_state) : «dfn'MULHSU» (7,1,2) (fixture s 0 4294967295 4294967295) = (let t := fixture s 0 4294967295 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (4294967295 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (4294967295 : BitVec 64))))), 7) (fixture s 0 4294967295 4294967295) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (4294967295 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (4294967295 : BitVec 64)))))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_0_5_0
example (s : riscv_state) : «dfn'MULHSU» (0,1,2) (fixture s 0 9223372036854775808 2) = (let t := fixture s 0 9223372036854775808 2; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (2 : BitVec 64))))), 0) (fixture s 0 9223372036854775808 2) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (2 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_0_5_1
example (s : riscv_state) : «dfn'MULHSU» (1,1,2) (fixture s 0 9223372036854775808 2) = (let t := fixture s 0 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (2 : BitVec 64))))), 1) (fixture s 0 9223372036854775808 2) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (2 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_0_5_2
example (s : riscv_state) : «dfn'MULHSU» (2,1,2) (fixture s 0 9223372036854775808 2) = (let t := fixture s 0 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (2 : BitVec 64))))), 2) (fixture s 0 9223372036854775808 2) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (2 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_0_5_7
example (s : riscv_state) : «dfn'MULHSU» (7,1,2) (fixture s 0 9223372036854775808 2) = (let t := fixture s 0 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (2 : BitVec 64))))), 7) (fixture s 0 9223372036854775808 2) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (2 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_0_6_0
example (s : riscv_state) : «dfn'MULHSU» (0,1,2) (fixture s 0 9223372036854775808 18446744073709551615) = (let t := fixture s 0 9223372036854775808 18446744073709551615; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))))), 0) (fixture s 0 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_0_6_1
example (s : riscv_state) : «dfn'MULHSU» (1,1,2) (fixture s 0 9223372036854775808 18446744073709551615) = (let t := fixture s 0 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))))), 1) (fixture s 0 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_0_6_2
example (s : riscv_state) : «dfn'MULHSU» (2,1,2) (fixture s 0 9223372036854775808 18446744073709551615) = (let t := fixture s 0 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))))), 2) (fixture s 0 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_0_6_7
example (s : riscv_state) : «dfn'MULHSU» (7,1,2) (fixture s 0 9223372036854775808 18446744073709551615) = (let t := fixture s 0 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))))), 7) (fixture s 0 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_0_7_0
example (s : riscv_state) : «dfn'MULHSU» (0,1,2) (fixture s 0 9223372036854775807 9223372036854775807) = (let t := fixture s 0 9223372036854775807 9223372036854775807; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (9223372036854775807 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775807 : BitVec 64))))), 0) (fixture s 0 9223372036854775807 9223372036854775807) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (9223372036854775807 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775807 : BitVec 64)))))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_0_7_1
example (s : riscv_state) : «dfn'MULHSU» (1,1,2) (fixture s 0 9223372036854775807 9223372036854775807) = (let t := fixture s 0 9223372036854775807 9223372036854775807; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (9223372036854775807 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775807 : BitVec 64))))), 1) (fixture s 0 9223372036854775807 9223372036854775807) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (9223372036854775807 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775807 : BitVec 64)))))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_0_7_2
example (s : riscv_state) : «dfn'MULHSU» (2,1,2) (fixture s 0 9223372036854775807 9223372036854775807) = (let t := fixture s 0 9223372036854775807 9223372036854775807; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (9223372036854775807 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775807 : BitVec 64))))), 2) (fixture s 0 9223372036854775807 9223372036854775807) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (9223372036854775807 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775807 : BitVec 64)))))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_0_7_7
example (s : riscv_state) : «dfn'MULHSU» (7,1,2) (fixture s 0 9223372036854775807 9223372036854775807) = (let t := fixture s 0 9223372036854775807 9223372036854775807; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (9223372036854775807 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775807 : BitVec 64))))), 7) (fixture s 0 9223372036854775807 9223372036854775807) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (9223372036854775807 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775807 : BitVec 64)))))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_0_8_0
example (s : riscv_state) : «dfn'MULHSU» (0,1,2) (fixture s 0 4294967297 4294967297) = (let t := fixture s 0 4294967297 4294967297; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (4294967297 : BitVec 64))))), 0) (fixture s 0 4294967297 4294967297) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (4294967297 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_0_8_1
example (s : riscv_state) : «dfn'MULHSU» (1,1,2) (fixture s 0 4294967297 4294967297) = (let t := fixture s 0 4294967297 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (4294967297 : BitVec 64))))), 1) (fixture s 0 4294967297 4294967297) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (4294967297 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_0_8_2
example (s : riscv_state) : «dfn'MULHSU» (2,1,2) (fixture s 0 4294967297 4294967297) = (let t := fixture s 0 4294967297 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (4294967297 : BitVec 64))))), 2) (fixture s 0 4294967297 4294967297) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (4294967297 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_0_8_7
example (s : riscv_state) : «dfn'MULHSU» (7,1,2) (fixture s 0 4294967297 4294967297) = (let t := fixture s 0 4294967297 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (4294967297 : BitVec 64))))), 7) (fixture s 0 4294967297 4294967297) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (4294967297 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_0_9_0
example (s : riscv_state) : «dfn'MULHSU» (0,0,2) (fixture s 0 17 18446744073709551615) = (let t := fixture s 0 17 18446744073709551615; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (0 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))))), 0) (fixture s 0 17 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (0 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_0_9_1
example (s : riscv_state) : «dfn'MULHSU» (1,0,2) (fixture s 0 17 18446744073709551615) = (let t := fixture s 0 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (0 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))))), 1) (fixture s 0 17 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (0 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_0_9_2
example (s : riscv_state) : «dfn'MULHSU» (2,0,2) (fixture s 0 17 18446744073709551615) = (let t := fixture s 0 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (0 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))))), 2) (fixture s 0 17 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (0 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_0_9_7
example (s : riscv_state) : «dfn'MULHSU» (7,0,2) (fixture s 0 17 18446744073709551615) = (let t := fixture s 0 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (0 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))))), 7) (fixture s 0 17 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (0 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_0_10_0
example (s : riscv_state) : «dfn'MULHSU» (0,1,0) (fixture s 0 18446744073709551615 17) = (let t := fixture s 0 18446744073709551615 17; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (0 : BitVec 64))))), 0) (fixture s 0 18446744073709551615 17) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (0 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_0_10_1
example (s : riscv_state) : «dfn'MULHSU» (1,1,0) (fixture s 0 18446744073709551615 17) = (let t := fixture s 0 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (0 : BitVec 64))))), 1) (fixture s 0 18446744073709551615 17) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (0 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_0_10_2
example (s : riscv_state) : «dfn'MULHSU» (2,1,0) (fixture s 0 18446744073709551615 17) = (let t := fixture s 0 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (0 : BitVec 64))))), 2) (fixture s 0 18446744073709551615 17) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (0 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_0_10_7
example (s : riscv_state) : «dfn'MULHSU» (7,1,0) (fixture s 0 18446744073709551615 17) = (let t := fixture s 0 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (0 : BitVec 64))))), 7) (fixture s 0 18446744073709551615 17) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (0 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_0_11_0
example (s : riscv_state) : «dfn'MULHSU» (0,1,1) (fixture s 0 9223372036854775809 18446744073709551615) = (let t := fixture s 0 9223372036854775809 18446744073709551615; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64))))), 0) (fixture s 0 9223372036854775809 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_0_11_1
example (s : riscv_state) : «dfn'MULHSU» (1,1,1) (fixture s 0 9223372036854775809 18446744073709551615) = (let t := fixture s 0 9223372036854775809 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64))))), 1) (fixture s 0 9223372036854775809 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_0_11_2
example (s : riscv_state) : «dfn'MULHSU» (2,1,1) (fixture s 0 9223372036854775809 18446744073709551615) = (let t := fixture s 0 9223372036854775809 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64))))), 2) (fixture s 0 9223372036854775809 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_0_11_7
example (s : riscv_state) : «dfn'MULHSU» (7,1,1) (fixture s 0 9223372036854775809 18446744073709551615) = (let t := fixture s 0 9223372036854775809 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64))))), 7) (fixture s 0 9223372036854775809 18446744073709551615) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 63 32 ((BitVec.signExtend 128 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64))) * (BitVec.setWidth 128 (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)))))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_2_0_0
example (s : riscv_state) : «dfn'MULHSU» (0,1,2) (fixture s 2 0 0) = (let t := fixture s 2 0 0; t) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64))), 0) (fixture s 2 0 0) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_2_0_1
example (s : riscv_state) : «dfn'MULHSU» (1,1,2) (fixture s 2 0 0) = (let t := fixture s 2 0 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64))), 1) (fixture s 2 0 0) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_2_0_2
example (s : riscv_state) : «dfn'MULHSU» (2,1,2) (fixture s 2 0 0) = (let t := fixture s 2 0 0; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64))), 2) (fixture s 2 0 0) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_2_0_7
example (s : riscv_state) : «dfn'MULHSU» (7,1,2) (fixture s 2 0 0) = (let t := fixture s 2 0 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64))), 7) (fixture s 2 0 0) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_2_1_0
example (s : riscv_state) : «dfn'MULHSU» (0,1,2) (fixture s 2 18446744073709551615 18446744073709551615) = (let t := fixture s 2 18446744073709551615 18446744073709551615; t) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64))), 0) (fixture s 2 18446744073709551615 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64)))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_2_1_1
example (s : riscv_state) : «dfn'MULHSU» (1,1,2) (fixture s 2 18446744073709551615 18446744073709551615) = (let t := fixture s 2 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64))), 1) (fixture s 2 18446744073709551615 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64)))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_2_1_2
example (s : riscv_state) : «dfn'MULHSU» (2,1,2) (fixture s 2 18446744073709551615 18446744073709551615) = (let t := fixture s 2 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64))), 2) (fixture s 2 18446744073709551615 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64)))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_2_1_7
example (s : riscv_state) : «dfn'MULHSU» (7,1,2) (fixture s 2 18446744073709551615 18446744073709551615) = (let t := fixture s 2 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64))), 7) (fixture s 2 18446744073709551615 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64)))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_2_2_0
example (s : riscv_state) : «dfn'MULHSU» (0,1,2) (fixture s 2 18446744073709551615 2) = (let t := fixture s 2 18446744073709551615 2; t) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64))), 0) (fixture s 2 18446744073709551615 2) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64)))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_2_2_1
example (s : riscv_state) : «dfn'MULHSU» (1,1,2) (fixture s 2 18446744073709551615 2) = (let t := fixture s 2 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64))), 1) (fixture s 2 18446744073709551615 2) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64)))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_2_2_2
example (s : riscv_state) : «dfn'MULHSU» (2,1,2) (fixture s 2 18446744073709551615 2) = (let t := fixture s 2 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64))), 2) (fixture s 2 18446744073709551615 2) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64)))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_2_2_7
example (s : riscv_state) : «dfn'MULHSU» (7,1,2) (fixture s 2 18446744073709551615 2) = (let t := fixture s 2 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64))), 7) (fixture s 2 18446744073709551615 2) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64)))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_2_3_0
example (s : riscv_state) : «dfn'MULHSU» (0,1,2) (fixture s 2 2147483648 2147483648) = (let t := fixture s 2 2147483648 2147483648; t) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (2147483648 : BitVec 64)) * (BitVec.setWidth 128 (2147483648 : BitVec 64))), 0) (fixture s 2 2147483648 2147483648) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (2147483648 : BitVec 64)) * (BitVec.setWidth 128 (2147483648 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_2_3_1
example (s : riscv_state) : «dfn'MULHSU» (1,1,2) (fixture s 2 2147483648 2147483648) = (let t := fixture s 2 2147483648 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (2147483648 : BitVec 64)) * (BitVec.setWidth 128 (2147483648 : BitVec 64))), 1) (fixture s 2 2147483648 2147483648) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (2147483648 : BitVec 64)) * (BitVec.setWidth 128 (2147483648 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_2_3_2
example (s : riscv_state) : «dfn'MULHSU» (2,1,2) (fixture s 2 2147483648 2147483648) = (let t := fixture s 2 2147483648 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (2147483648 : BitVec 64)) * (BitVec.setWidth 128 (2147483648 : BitVec 64))), 2) (fixture s 2 2147483648 2147483648) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (2147483648 : BitVec 64)) * (BitVec.setWidth 128 (2147483648 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_2_3_7
example (s : riscv_state) : «dfn'MULHSU» (7,1,2) (fixture s 2 2147483648 2147483648) = (let t := fixture s 2 2147483648 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (2147483648 : BitVec 64)) * (BitVec.setWidth 128 (2147483648 : BitVec 64))), 7) (fixture s 2 2147483648 2147483648) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (2147483648 : BitVec 64)) * (BitVec.setWidth 128 (2147483648 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_2_4_0
example (s : riscv_state) : «dfn'MULHSU» (0,1,2) (fixture s 2 4294967295 4294967295) = (let t := fixture s 2 4294967295 4294967295; t) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967295 : BitVec 64)) * (BitVec.setWidth 128 (4294967295 : BitVec 64))), 0) (fixture s 2 4294967295 4294967295) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967295 : BitVec 64)) * (BitVec.setWidth 128 (4294967295 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_2_4_1
example (s : riscv_state) : «dfn'MULHSU» (1,1,2) (fixture s 2 4294967295 4294967295) = (let t := fixture s 2 4294967295 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967295 : BitVec 64)) * (BitVec.setWidth 128 (4294967295 : BitVec 64))), 1) (fixture s 2 4294967295 4294967295) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967295 : BitVec 64)) * (BitVec.setWidth 128 (4294967295 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_2_4_2
example (s : riscv_state) : «dfn'MULHSU» (2,1,2) (fixture s 2 4294967295 4294967295) = (let t := fixture s 2 4294967295 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967295 : BitVec 64)) * (BitVec.setWidth 128 (4294967295 : BitVec 64))), 2) (fixture s 2 4294967295 4294967295) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967295 : BitVec 64)) * (BitVec.setWidth 128 (4294967295 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_2_4_7
example (s : riscv_state) : «dfn'MULHSU» (7,1,2) (fixture s 2 4294967295 4294967295) = (let t := fixture s 2 4294967295 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967295 : BitVec 64)) * (BitVec.setWidth 128 (4294967295 : BitVec 64))), 7) (fixture s 2 4294967295 4294967295) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967295 : BitVec 64)) * (BitVec.setWidth 128 (4294967295 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_2_5_0
example (s : riscv_state) : «dfn'MULHSU» (0,1,2) (fixture s 2 9223372036854775808 2) = (let t := fixture s 2 9223372036854775808 2; t) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64))), 0) (fixture s 2 9223372036854775808 2) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64)))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_2_5_1
example (s : riscv_state) : «dfn'MULHSU» (1,1,2) (fixture s 2 9223372036854775808 2) = (let t := fixture s 2 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64))), 1) (fixture s 2 9223372036854775808 2) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64)))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_2_5_2
example (s : riscv_state) : «dfn'MULHSU» (2,1,2) (fixture s 2 9223372036854775808 2) = (let t := fixture s 2 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64))), 2) (fixture s 2 9223372036854775808 2) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64)))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_2_5_7
example (s : riscv_state) : «dfn'MULHSU» (7,1,2) (fixture s 2 9223372036854775808 2) = (let t := fixture s 2 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64))), 7) (fixture s 2 9223372036854775808 2) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64)))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_2_6_0
example (s : riscv_state) : «dfn'MULHSU» (0,1,2) (fixture s 2 9223372036854775808 18446744073709551615) = (let t := fixture s 2 9223372036854775808 18446744073709551615; t) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64))), 0) (fixture s 2 9223372036854775808 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64)))) = (9223372036854775808 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_2_6_1
example (s : riscv_state) : «dfn'MULHSU» (1,1,2) (fixture s 2 9223372036854775808 18446744073709551615) = (let t := fixture s 2 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64))), 1) (fixture s 2 9223372036854775808 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64)))) = (9223372036854775808 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_2_6_2
example (s : riscv_state) : «dfn'MULHSU» (2,1,2) (fixture s 2 9223372036854775808 18446744073709551615) = (let t := fixture s 2 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64))), 2) (fixture s 2 9223372036854775808 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64)))) = (9223372036854775808 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_2_6_7
example (s : riscv_state) : «dfn'MULHSU» (7,1,2) (fixture s 2 9223372036854775808 18446744073709551615) = (let t := fixture s 2 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64))), 7) (fixture s 2 9223372036854775808 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64)))) = (9223372036854775808 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_2_7_0
example (s : riscv_state) : «dfn'MULHSU» (0,1,2) (fixture s 2 9223372036854775807 9223372036854775807) = (let t := fixture s 2 9223372036854775807 9223372036854775807; t) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775807 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775807 : BitVec 64))), 0) (fixture s 2 9223372036854775807 9223372036854775807) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775807 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775807 : BitVec 64)))) = (4611686018427387903 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_2_7_1
example (s : riscv_state) : «dfn'MULHSU» (1,1,2) (fixture s 2 9223372036854775807 9223372036854775807) = (let t := fixture s 2 9223372036854775807 9223372036854775807; {t with c_gpr := holUpdate 7 (holUpdate 1 4611686018427387903 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775807 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775807 : BitVec 64))), 1) (fixture s 2 9223372036854775807 9223372036854775807) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775807 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775807 : BitVec 64)))) = (4611686018427387903 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_2_7_2
example (s : riscv_state) : «dfn'MULHSU» (2,1,2) (fixture s 2 9223372036854775807 9223372036854775807) = (let t := fixture s 2 9223372036854775807 9223372036854775807; {t with c_gpr := holUpdate 7 (holUpdate 2 4611686018427387903 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775807 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775807 : BitVec 64))), 2) (fixture s 2 9223372036854775807 9223372036854775807) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775807 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775807 : BitVec 64)))) = (4611686018427387903 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_2_7_7
example (s : riscv_state) : «dfn'MULHSU» (7,1,2) (fixture s 2 9223372036854775807 9223372036854775807) = (let t := fixture s 2 9223372036854775807 9223372036854775807; {t with c_gpr := holUpdate 7 (holUpdate 7 4611686018427387903 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775807 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775807 : BitVec 64))), 7) (fixture s 2 9223372036854775807 9223372036854775807) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775807 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775807 : BitVec 64)))) = (4611686018427387903 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_2_8_0
example (s : riscv_state) : «dfn'MULHSU» (0,1,2) (fixture s 2 4294967297 4294967297) = (let t := fixture s 2 4294967297 4294967297; t) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967297 : BitVec 64)) * (BitVec.setWidth 128 (4294967297 : BitVec 64))), 0) (fixture s 2 4294967297 4294967297) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967297 : BitVec 64)) * (BitVec.setWidth 128 (4294967297 : BitVec 64)))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_2_8_1
example (s : riscv_state) : «dfn'MULHSU» (1,1,2) (fixture s 2 4294967297 4294967297) = (let t := fixture s 2 4294967297 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967297 : BitVec 64)) * (BitVec.setWidth 128 (4294967297 : BitVec 64))), 1) (fixture s 2 4294967297 4294967297) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967297 : BitVec 64)) * (BitVec.setWidth 128 (4294967297 : BitVec 64)))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_2_8_2
example (s : riscv_state) : «dfn'MULHSU» (2,1,2) (fixture s 2 4294967297 4294967297) = (let t := fixture s 2 4294967297 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967297 : BitVec 64)) * (BitVec.setWidth 128 (4294967297 : BitVec 64))), 2) (fixture s 2 4294967297 4294967297) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967297 : BitVec 64)) * (BitVec.setWidth 128 (4294967297 : BitVec 64)))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_2_8_7
example (s : riscv_state) : «dfn'MULHSU» (7,1,2) (fixture s 2 4294967297 4294967297) = (let t := fixture s 2 4294967297 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967297 : BitVec 64)) * (BitVec.setWidth 128 (4294967297 : BitVec 64))), 7) (fixture s 2 4294967297 4294967297) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967297 : BitVec 64)) * (BitVec.setWidth 128 (4294967297 : BitVec 64)))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_2_9_0
example (s : riscv_state) : «dfn'MULHSU» (0,0,2) (fixture s 2 17 18446744073709551615) = (let t := fixture s 2 17 18446744073709551615; t) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64))), 0) (fixture s 2 17 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_2_9_1
example (s : riscv_state) : «dfn'MULHSU» (1,0,2) (fixture s 2 17 18446744073709551615) = (let t := fixture s 2 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64))), 1) (fixture s 2 17 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_2_9_2
example (s : riscv_state) : «dfn'MULHSU» (2,0,2) (fixture s 2 17 18446744073709551615) = (let t := fixture s 2 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64))), 2) (fixture s 2 17 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_2_9_7
example (s : riscv_state) : «dfn'MULHSU» (7,0,2) (fixture s 2 17 18446744073709551615) = (let t := fixture s 2 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64))), 7) (fixture s 2 17 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_2_10_0
example (s : riscv_state) : «dfn'MULHSU» (0,1,0) (fixture s 2 18446744073709551615 17) = (let t := fixture s 2 18446744073709551615 17; t) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64))), 0) (fixture s 2 18446744073709551615 17) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_2_10_1
example (s : riscv_state) : «dfn'MULHSU» (1,1,0) (fixture s 2 18446744073709551615 17) = (let t := fixture s 2 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64))), 1) (fixture s 2 18446744073709551615 17) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_2_10_2
example (s : riscv_state) : «dfn'MULHSU» (2,1,0) (fixture s 2 18446744073709551615 17) = (let t := fixture s 2 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64))), 2) (fixture s 2 18446744073709551615 17) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_2_10_7
example (s : riscv_state) : «dfn'MULHSU» (7,1,0) (fixture s 2 18446744073709551615 17) = (let t := fixture s 2 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64))), 7) (fixture s 2 18446744073709551615 17) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_2_11_0
example (s : riscv_state) : «dfn'MULHSU» (0,1,1) (fixture s 2 9223372036854775809 18446744073709551615) = (let t := fixture s 2 9223372036854775809 18446744073709551615; t) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775809 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775809 : BitVec 64))), 0) (fixture s 2 9223372036854775809 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775809 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775809 : BitVec 64)))) = (13835058055282163712 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_2_11_1
example (s : riscv_state) : «dfn'MULHSU» (1,1,1) (fixture s 2 9223372036854775809 18446744073709551615) = (let t := fixture s 2 9223372036854775809 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 13835058055282163712 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775809 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775809 : BitVec 64))), 1) (fixture s 2 9223372036854775809 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775809 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775809 : BitVec 64)))) = (13835058055282163712 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_2_11_2
example (s : riscv_state) : «dfn'MULHSU» (2,1,1) (fixture s 2 9223372036854775809 18446744073709551615) = (let t := fixture s 2 9223372036854775809 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 13835058055282163712 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775809 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775809 : BitVec 64))), 2) (fixture s 2 9223372036854775809 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775809 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775809 : BitVec 64)))) = (13835058055282163712 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_2_11_7
example (s : riscv_state) : «dfn'MULHSU» (7,1,1) (fixture s 2 9223372036854775809 18446744073709551615) = (let t := fixture s 2 9223372036854775809 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 13835058055282163712 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775809 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775809 : BitVec 64))), 7) (fixture s 2 9223372036854775809 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775809 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775809 : BitVec 64)))) = (13835058055282163712 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_3_0_0
example (s : riscv_state) : «dfn'MULHSU» (0,1,2) (fixture s 3 0 0) = (let t := fixture s 3 0 0; t) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64))), 0) (fixture s 3 0 0) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_3_0_1
example (s : riscv_state) : «dfn'MULHSU» (1,1,2) (fixture s 3 0 0) = (let t := fixture s 3 0 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64))), 1) (fixture s 3 0 0) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_3_0_2
example (s : riscv_state) : «dfn'MULHSU» (2,1,2) (fixture s 3 0 0) = (let t := fixture s 3 0 0; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64))), 2) (fixture s 3 0 0) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_3_0_7
example (s : riscv_state) : «dfn'MULHSU» (7,1,2) (fixture s 3 0 0) = (let t := fixture s 3 0 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64))), 7) (fixture s 3 0 0) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_3_1_0
example (s : riscv_state) : «dfn'MULHSU» (0,1,2) (fixture s 3 18446744073709551615 18446744073709551615) = (let t := fixture s 3 18446744073709551615 18446744073709551615; t) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64))), 0) (fixture s 3 18446744073709551615 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64)))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_3_1_1
example (s : riscv_state) : «dfn'MULHSU» (1,1,2) (fixture s 3 18446744073709551615 18446744073709551615) = (let t := fixture s 3 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64))), 1) (fixture s 3 18446744073709551615 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64)))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_3_1_2
example (s : riscv_state) : «dfn'MULHSU» (2,1,2) (fixture s 3 18446744073709551615 18446744073709551615) = (let t := fixture s 3 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64))), 2) (fixture s 3 18446744073709551615 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64)))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_3_1_7
example (s : riscv_state) : «dfn'MULHSU» (7,1,2) (fixture s 3 18446744073709551615 18446744073709551615) = (let t := fixture s 3 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64))), 7) (fixture s 3 18446744073709551615 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64)))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_3_2_0
example (s : riscv_state) : «dfn'MULHSU» (0,1,2) (fixture s 3 18446744073709551615 2) = (let t := fixture s 3 18446744073709551615 2; t) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64))), 0) (fixture s 3 18446744073709551615 2) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64)))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_3_2_1
example (s : riscv_state) : «dfn'MULHSU» (1,1,2) (fixture s 3 18446744073709551615 2) = (let t := fixture s 3 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64))), 1) (fixture s 3 18446744073709551615 2) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64)))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_3_2_2
example (s : riscv_state) : «dfn'MULHSU» (2,1,2) (fixture s 3 18446744073709551615 2) = (let t := fixture s 3 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64))), 2) (fixture s 3 18446744073709551615 2) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64)))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_3_2_7
example (s : riscv_state) : «dfn'MULHSU» (7,1,2) (fixture s 3 18446744073709551615 2) = (let t := fixture s 3 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64))), 7) (fixture s 3 18446744073709551615 2) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64)))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_3_3_0
example (s : riscv_state) : «dfn'MULHSU» (0,1,2) (fixture s 3 2147483648 2147483648) = (let t := fixture s 3 2147483648 2147483648; t) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (2147483648 : BitVec 64)) * (BitVec.setWidth 128 (2147483648 : BitVec 64))), 0) (fixture s 3 2147483648 2147483648) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (2147483648 : BitVec 64)) * (BitVec.setWidth 128 (2147483648 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_3_3_1
example (s : riscv_state) : «dfn'MULHSU» (1,1,2) (fixture s 3 2147483648 2147483648) = (let t := fixture s 3 2147483648 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (2147483648 : BitVec 64)) * (BitVec.setWidth 128 (2147483648 : BitVec 64))), 1) (fixture s 3 2147483648 2147483648) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (2147483648 : BitVec 64)) * (BitVec.setWidth 128 (2147483648 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_3_3_2
example (s : riscv_state) : «dfn'MULHSU» (2,1,2) (fixture s 3 2147483648 2147483648) = (let t := fixture s 3 2147483648 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (2147483648 : BitVec 64)) * (BitVec.setWidth 128 (2147483648 : BitVec 64))), 2) (fixture s 3 2147483648 2147483648) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (2147483648 : BitVec 64)) * (BitVec.setWidth 128 (2147483648 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_3_3_7
example (s : riscv_state) : «dfn'MULHSU» (7,1,2) (fixture s 3 2147483648 2147483648) = (let t := fixture s 3 2147483648 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (2147483648 : BitVec 64)) * (BitVec.setWidth 128 (2147483648 : BitVec 64))), 7) (fixture s 3 2147483648 2147483648) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (2147483648 : BitVec 64)) * (BitVec.setWidth 128 (2147483648 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_3_4_0
example (s : riscv_state) : «dfn'MULHSU» (0,1,2) (fixture s 3 4294967295 4294967295) = (let t := fixture s 3 4294967295 4294967295; t) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967295 : BitVec 64)) * (BitVec.setWidth 128 (4294967295 : BitVec 64))), 0) (fixture s 3 4294967295 4294967295) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967295 : BitVec 64)) * (BitVec.setWidth 128 (4294967295 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_3_4_1
example (s : riscv_state) : «dfn'MULHSU» (1,1,2) (fixture s 3 4294967295 4294967295) = (let t := fixture s 3 4294967295 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967295 : BitVec 64)) * (BitVec.setWidth 128 (4294967295 : BitVec 64))), 1) (fixture s 3 4294967295 4294967295) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967295 : BitVec 64)) * (BitVec.setWidth 128 (4294967295 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_3_4_2
example (s : riscv_state) : «dfn'MULHSU» (2,1,2) (fixture s 3 4294967295 4294967295) = (let t := fixture s 3 4294967295 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967295 : BitVec 64)) * (BitVec.setWidth 128 (4294967295 : BitVec 64))), 2) (fixture s 3 4294967295 4294967295) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967295 : BitVec 64)) * (BitVec.setWidth 128 (4294967295 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_3_4_7
example (s : riscv_state) : «dfn'MULHSU» (7,1,2) (fixture s 3 4294967295 4294967295) = (let t := fixture s 3 4294967295 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967295 : BitVec 64)) * (BitVec.setWidth 128 (4294967295 : BitVec 64))), 7) (fixture s 3 4294967295 4294967295) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967295 : BitVec 64)) * (BitVec.setWidth 128 (4294967295 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_3_5_0
example (s : riscv_state) : «dfn'MULHSU» (0,1,2) (fixture s 3 9223372036854775808 2) = (let t := fixture s 3 9223372036854775808 2; t) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64))), 0) (fixture s 3 9223372036854775808 2) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64)))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_3_5_1
example (s : riscv_state) : «dfn'MULHSU» (1,1,2) (fixture s 3 9223372036854775808 2) = (let t := fixture s 3 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64))), 1) (fixture s 3 9223372036854775808 2) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64)))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_3_5_2
example (s : riscv_state) : «dfn'MULHSU» (2,1,2) (fixture s 3 9223372036854775808 2) = (let t := fixture s 3 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64))), 2) (fixture s 3 9223372036854775808 2) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64)))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_3_5_7
example (s : riscv_state) : «dfn'MULHSU» (7,1,2) (fixture s 3 9223372036854775808 2) = (let t := fixture s 3 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64))), 7) (fixture s 3 9223372036854775808 2) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (2 : BitVec 64)))) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_3_6_0
example (s : riscv_state) : «dfn'MULHSU» (0,1,2) (fixture s 3 9223372036854775808 18446744073709551615) = (let t := fixture s 3 9223372036854775808 18446744073709551615; t) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64))), 0) (fixture s 3 9223372036854775808 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64)))) = (9223372036854775808 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_3_6_1
example (s : riscv_state) : «dfn'MULHSU» (1,1,2) (fixture s 3 9223372036854775808 18446744073709551615) = (let t := fixture s 3 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64))), 1) (fixture s 3 9223372036854775808 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64)))) = (9223372036854775808 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_3_6_2
example (s : riscv_state) : «dfn'MULHSU» (2,1,2) (fixture s 3 9223372036854775808 18446744073709551615) = (let t := fixture s 3 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64))), 2) (fixture s 3 9223372036854775808 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64)))) = (9223372036854775808 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_3_6_7
example (s : riscv_state) : «dfn'MULHSU» (7,1,2) (fixture s 3 9223372036854775808 18446744073709551615) = (let t := fixture s 3 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64))), 7) (fixture s 3 9223372036854775808 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775808 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64)))) = (9223372036854775808 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_3_7_0
example (s : riscv_state) : «dfn'MULHSU» (0,1,2) (fixture s 3 9223372036854775807 9223372036854775807) = (let t := fixture s 3 9223372036854775807 9223372036854775807; t) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775807 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775807 : BitVec 64))), 0) (fixture s 3 9223372036854775807 9223372036854775807) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775807 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775807 : BitVec 64)))) = (4611686018427387903 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_3_7_1
example (s : riscv_state) : «dfn'MULHSU» (1,1,2) (fixture s 3 9223372036854775807 9223372036854775807) = (let t := fixture s 3 9223372036854775807 9223372036854775807; {t with c_gpr := holUpdate 7 (holUpdate 1 4611686018427387903 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775807 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775807 : BitVec 64))), 1) (fixture s 3 9223372036854775807 9223372036854775807) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775807 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775807 : BitVec 64)))) = (4611686018427387903 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_3_7_2
example (s : riscv_state) : «dfn'MULHSU» (2,1,2) (fixture s 3 9223372036854775807 9223372036854775807) = (let t := fixture s 3 9223372036854775807 9223372036854775807; {t with c_gpr := holUpdate 7 (holUpdate 2 4611686018427387903 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775807 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775807 : BitVec 64))), 2) (fixture s 3 9223372036854775807 9223372036854775807) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775807 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775807 : BitVec 64)))) = (4611686018427387903 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_3_7_7
example (s : riscv_state) : «dfn'MULHSU» (7,1,2) (fixture s 3 9223372036854775807 9223372036854775807) = (let t := fixture s 3 9223372036854775807 9223372036854775807; {t with c_gpr := holUpdate 7 (holUpdate 7 4611686018427387903 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775807 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775807 : BitVec 64))), 7) (fixture s 3 9223372036854775807 9223372036854775807) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775807 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775807 : BitVec 64)))) = (4611686018427387903 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_3_8_0
example (s : riscv_state) : «dfn'MULHSU» (0,1,2) (fixture s 3 4294967297 4294967297) = (let t := fixture s 3 4294967297 4294967297; t) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967297 : BitVec 64)) * (BitVec.setWidth 128 (4294967297 : BitVec 64))), 0) (fixture s 3 4294967297 4294967297) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967297 : BitVec 64)) * (BitVec.setWidth 128 (4294967297 : BitVec 64)))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_3_8_1
example (s : riscv_state) : «dfn'MULHSU» (1,1,2) (fixture s 3 4294967297 4294967297) = (let t := fixture s 3 4294967297 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967297 : BitVec 64)) * (BitVec.setWidth 128 (4294967297 : BitVec 64))), 1) (fixture s 3 4294967297 4294967297) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967297 : BitVec 64)) * (BitVec.setWidth 128 (4294967297 : BitVec 64)))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_3_8_2
example (s : riscv_state) : «dfn'MULHSU» (2,1,2) (fixture s 3 4294967297 4294967297) = (let t := fixture s 3 4294967297 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967297 : BitVec 64)) * (BitVec.setWidth 128 (4294967297 : BitVec 64))), 2) (fixture s 3 4294967297 4294967297) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967297 : BitVec 64)) * (BitVec.setWidth 128 (4294967297 : BitVec 64)))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_3_8_7
example (s : riscv_state) : «dfn'MULHSU» (7,1,2) (fixture s 3 4294967297 4294967297) = (let t := fixture s 3 4294967297 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967297 : BitVec 64)) * (BitVec.setWidth 128 (4294967297 : BitVec 64))), 7) (fixture s 3 4294967297 4294967297) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (4294967297 : BitVec 64)) * (BitVec.setWidth 128 (4294967297 : BitVec 64)))) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_3_9_0
example (s : riscv_state) : «dfn'MULHSU» (0,0,2) (fixture s 3 17 18446744073709551615) = (let t := fixture s 3 17 18446744073709551615; t) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64))), 0) (fixture s 3 17 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_3_9_1
example (s : riscv_state) : «dfn'MULHSU» (1,0,2) (fixture s 3 17 18446744073709551615) = (let t := fixture s 3 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64))), 1) (fixture s 3 17 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_3_9_2
example (s : riscv_state) : «dfn'MULHSU» (2,0,2) (fixture s 3 17 18446744073709551615) = (let t := fixture s 3 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64))), 2) (fixture s 3 17 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_3_9_7
example (s : riscv_state) : «dfn'MULHSU» (7,0,2) (fixture s 3 17 18446744073709551615) = (let t := fixture s 3 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64))), 7) (fixture s 3 17 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (0 : BitVec 64)) * (BitVec.setWidth 128 (18446744073709551615 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_3_10_0
example (s : riscv_state) : «dfn'MULHSU» (0,1,0) (fixture s 3 18446744073709551615 17) = (let t := fixture s 3 18446744073709551615 17; t) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64))), 0) (fixture s 3 18446744073709551615 17) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_3_10_1
example (s : riscv_state) : «dfn'MULHSU» (1,1,0) (fixture s 3 18446744073709551615 17) = (let t := fixture s 3 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64))), 1) (fixture s 3 18446744073709551615 17) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_3_10_2
example (s : riscv_state) : «dfn'MULHSU» (2,1,0) (fixture s 3 18446744073709551615 17) = (let t := fixture s 3 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64))), 2) (fixture s 3 18446744073709551615 17) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_3_10_7
example (s : riscv_state) : «dfn'MULHSU» (7,1,0) (fixture s 3 18446744073709551615 17) = (let t := fixture s 3 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64))), 7) (fixture s 3 18446744073709551615 17) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (18446744073709551615 : BitVec 64)) * (BitVec.setWidth 128 (0 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_3_11_0
example (s : riscv_state) : «dfn'MULHSU» (0,1,1) (fixture s 3 9223372036854775809 18446744073709551615) = (let t := fixture s 3 9223372036854775809 18446744073709551615; t) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775809 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775809 : BitVec 64))), 0) (fixture s 3 9223372036854775809 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775809 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775809 : BitVec 64)))) = (13835058055282163712 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_3_11_1
example (s : riscv_state) : «dfn'MULHSU» (1,1,1) (fixture s 3 9223372036854775809 18446744073709551615) = (let t := fixture s 3 9223372036854775809 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 13835058055282163712 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775809 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775809 : BitVec 64))), 1) (fixture s 3 9223372036854775809 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775809 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775809 : BitVec 64)))) = (13835058055282163712 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_3_11_2
example (s : riscv_state) : «dfn'MULHSU» (2,1,1) (fixture s 3 9223372036854775809 18446744073709551615) = (let t := fixture s 3 9223372036854775809 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 13835058055282163712 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775809 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775809 : BitVec 64))), 2) (fixture s 3 9223372036854775809 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775809 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775809 : BitVec 64)))) = (13835058055282163712 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_MULHSU_3_11_7
example (s : riscv_state) : «dfn'MULHSU» (7,1,1) (fixture s 3 9223372036854775809 18446744073709551615) = (let t := fixture s 3 9223372036854775809 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 13835058055282163712 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775809 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775809 : BitVec 64))), 7) (fixture s 3 9223372036854775809 18446744073709551615) = _
 have numeric : (holWordExtract 64 127 64 ((BitVec.signExtend 128 (9223372036854775809 : BitVec 64)) * (BitVec.setWidth 128 (9223372036854775809 : BitVec 64)))) = (13835058055282163712 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- multiply_symbolic_MUL_0
example (s : riscv_state) : «dfn'MUL» (0,0,0) ({fixture s 1 17 9 with exception := exception.NoException}) = ({fixture s 1 17 9 with exception := exception.NoException}) := by rfl

-- multiply_symbolic_MUL_1
example (s : riscv_state) : «dfn'MUL» (0,0,0) ({fixture s 1 17 9 with exception := exception.UNDEFINED [9]}) = ({fixture s 1 17 9 with exception := exception.UNDEFINED [9]}) := by rfl

-- multiply_symbolic_MULH_0
example (s : riscv_state) : «dfn'MULH» (0,0,0) ({fixture s 1 17 9 with exception := exception.NoException}) = (match in32BitMode () ({fixture s 1 17 9 with exception := exception.NoException}) with | (_,u) => match in32BitMode () u with | (_,u1) => match in32BitMode () u1 with | (_,u2) => u2) := by rfl

-- multiply_symbolic_MULH_1
example (s : riscv_state) : «dfn'MULH» (0,0,0) ({fixture s 1 17 9 with exception := exception.UNDEFINED [9]}) = (match in32BitMode () ({fixture s 1 17 9 with exception := exception.UNDEFINED [9]}) with | (_,u) => match in32BitMode () u with | (_,u1) => match in32BitMode () u1 with | (_,u2) => u2) := by rfl

-- multiply_symbolic_MULHU_0
example (s : riscv_state) : «dfn'MULHU» (0,0,0) ({fixture s 1 17 9 with exception := exception.NoException}) = (match in32BitMode () ({fixture s 1 17 9 with exception := exception.NoException}) with | (_,u) => match in32BitMode () u with | (_,u1) => match in32BitMode () u1 with | (_,u2) => u2) := by rfl

-- multiply_symbolic_MULHU_1
example (s : riscv_state) : «dfn'MULHU» (0,0,0) ({fixture s 1 17 9 with exception := exception.UNDEFINED [9]}) = (match in32BitMode () ({fixture s 1 17 9 with exception := exception.UNDEFINED [9]}) with | (_,u) => match in32BitMode () u with | (_,u1) => match in32BitMode () u1 with | (_,u2) => u2) := by rfl

-- multiply_symbolic_MULHSU_0
example (s : riscv_state) : «dfn'MULHSU» (0,0,0) ({fixture s 1 17 9 with exception := exception.NoException}) = (match in32BitMode () ({fixture s 1 17 9 with exception := exception.NoException}) with | (_,u) => match in32BitMode () u with | (_,u1) => match in32BitMode () u1 with | (_,u2) => u2) := by rfl

-- multiply_symbolic_MULHSU_1
example (s : riscv_state) : «dfn'MULHSU» (0,0,0) ({fixture s 1 17 9 with exception := exception.UNDEFINED [9]}) = (match in32BitMode () ({fixture s 1 17 9 with exception := exception.UNDEFINED [9]}) with | (_,u) => match in32BitMode () u with | (_,u1) => match in32BitMode () u1 with | (_,u2) => u2) := by rfl

end Flapjack.Test.L3MultiplyParity
