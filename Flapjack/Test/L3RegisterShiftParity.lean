import Flapjack.RiscV.L3.Defs.RegisterShift

set_option maxRecDepth 20000
namespace Flapjack.Test.L3RegisterShiftParity
open Flapjack.RiscV.L3
private def fixture (s : riscv_state) (mode : BitVec 2) (lhs rhs : BitVec 64) : riscv_state :=
 {s with procID := 7, c_MCSR := fun id => {s.c_MCSR id with mcpuid := {(s.c_MCSR id).mcpuid with ArchBase := mode}}, c_gpr := fun id r => if r = 1 then lhs else if r = 2 then rhs else s.c_gpr id r}

-- register_shift_SLL_0_0_0
example (s : riscv_state) : «dfn'SLL» (0,1,2) (fixture s 0 9223372036854775808 0) =
 (let t := fixture s 0 9223372036854775808 0; t) := by
  change «write'GPR» (((9223372036854775808 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 0) (fixture s 0 9223372036854775808 0) = _
  have numeric : (((9223372036854775808 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_0_0_1
example (s : riscv_state) : «dfn'SLL» (1,1,2) (fixture s 0 9223372036854775808 0) =
 (let t := fixture s 0 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 1 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775808 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 1) (fixture s 0 9223372036854775808 0) = _
  have numeric : (((9223372036854775808 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_0_0_2
example (s : riscv_state) : «dfn'SLL» (2,1,2) (fixture s 0 9223372036854775808 0) =
 (let t := fixture s 0 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 2 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775808 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 2) (fixture s 0 9223372036854775808 0) = _
  have numeric : (((9223372036854775808 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_0_0_7
example (s : riscv_state) : «dfn'SLL» (7,1,2) (fixture s 0 9223372036854775808 0) =
 (let t := fixture s 0 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 7 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775808 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 7) (fixture s 0 9223372036854775808 0) = _
  have numeric : (((9223372036854775808 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_0_1_0
example (s : riscv_state) : «dfn'SLL» (0,1,2) (fixture s 0 2147483649 31) =
 (let t := fixture s 0 2147483649 31; t) := by
  change «write'GPR» (((2147483649 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 0) (fixture s 0 2147483649 31) = _
  have numeric : (((2147483649 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (4611686020574871552 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_0_1_1
example (s : riscv_state) : «dfn'SLL» (1,1,2) (fixture s 0 2147483649 31) =
 (let t := fixture s 0 2147483649 31; {t with c_gpr := holUpdate 7 (holUpdate 1 4611686020574871552 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((2147483649 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 1) (fixture s 0 2147483649 31) = _
  have numeric : (((2147483649 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (4611686020574871552 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_0_1_2
example (s : riscv_state) : «dfn'SLL» (2,1,2) (fixture s 0 2147483649 31) =
 (let t := fixture s 0 2147483649 31; {t with c_gpr := holUpdate 7 (holUpdate 2 4611686020574871552 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((2147483649 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 2) (fixture s 0 2147483649 31) = _
  have numeric : (((2147483649 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (4611686020574871552 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_0_1_7
example (s : riscv_state) : «dfn'SLL» (7,1,2) (fixture s 0 2147483649 31) =
 (let t := fixture s 0 2147483649 31; {t with c_gpr := holUpdate 7 (holUpdate 7 4611686020574871552 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((2147483649 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 7) (fixture s 0 2147483649 31) = _
  have numeric : (((2147483649 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (4611686020574871552 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_0_2_0
example (s : riscv_state) : «dfn'SLL» (0,1,2) (fixture s 0 4294967297 32) =
 (let t := fixture s 0 4294967297 32; t) := by
  change «write'GPR» (((4294967297 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat), 0) (fixture s 0 4294967297 32) = _
  have numeric : (((4294967297 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat)) = (4294967297 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_0_2_1
example (s : riscv_state) : «dfn'SLL» (1,1,2) (fixture s 0 4294967297 32) =
 (let t := fixture s 0 4294967297 32; {t with c_gpr := holUpdate 7 (holUpdate 1 4294967297 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((4294967297 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat), 1) (fixture s 0 4294967297 32) = _
  have numeric : (((4294967297 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat)) = (4294967297 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_0_2_2
example (s : riscv_state) : «dfn'SLL» (2,1,2) (fixture s 0 4294967297 32) =
 (let t := fixture s 0 4294967297 32; {t with c_gpr := holUpdate 7 (holUpdate 2 4294967297 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((4294967297 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat), 2) (fixture s 0 4294967297 32) = _
  have numeric : (((4294967297 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat)) = (4294967297 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_0_2_7
example (s : riscv_state) : «dfn'SLL» (7,1,2) (fixture s 0 4294967297 32) =
 (let t := fixture s 0 4294967297 32; {t with c_gpr := holUpdate 7 (holUpdate 7 4294967297 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((4294967297 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat), 7) (fixture s 0 4294967297 32) = _
  have numeric : (((4294967297 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat)) = (4294967297 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_0_3_0
example (s : riscv_state) : «dfn'SLL» (0,1,2) (fixture s 0 18446744073709551615 63) =
 (let t := fixture s 0 18446744073709551615 63; t) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat), 0) (fixture s 0 18446744073709551615 63) = _
  have numeric : (((18446744073709551615 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_0_3_1
example (s : riscv_state) : «dfn'SLL» (1,1,2) (fixture s 0 18446744073709551615 63) =
 (let t := fixture s 0 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat), 1) (fixture s 0 18446744073709551615 63) = _
  have numeric : (((18446744073709551615 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_0_3_2
example (s : riscv_state) : «dfn'SLL» (2,1,2) (fixture s 0 18446744073709551615 63) =
 (let t := fixture s 0 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat), 2) (fixture s 0 18446744073709551615 63) = _
  have numeric : (((18446744073709551615 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_0_3_7
example (s : riscv_state) : «dfn'SLL» (7,1,2) (fixture s 0 18446744073709551615 63) =
 (let t := fixture s 0 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat), 7) (fixture s 0 18446744073709551615 63) = _
  have numeric : (((18446744073709551615 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_0_4_0
example (s : riscv_state) : «dfn'SLL» (0,1,2) (fixture s 0 2147483648 64) =
 (let t := fixture s 0 2147483648 64; t) := by
  change «write'GPR» (((2147483648 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat), 0) (fixture s 0 2147483648 64) = _
  have numeric : (((2147483648 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_0_4_1
example (s : riscv_state) : «dfn'SLL» (1,1,2) (fixture s 0 2147483648 64) =
 (let t := fixture s 0 2147483648 64; {t with c_gpr := holUpdate 7 (holUpdate 1 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((2147483648 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat), 1) (fixture s 0 2147483648 64) = _
  have numeric : (((2147483648 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_0_4_2
example (s : riscv_state) : «dfn'SLL» (2,1,2) (fixture s 0 2147483648 64) =
 (let t := fixture s 0 2147483648 64; {t with c_gpr := holUpdate 7 (holUpdate 2 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((2147483648 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat), 2) (fixture s 0 2147483648 64) = _
  have numeric : (((2147483648 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_0_4_7
example (s : riscv_state) : «dfn'SLL» (7,1,2) (fixture s 0 2147483648 64) =
 (let t := fixture s 0 2147483648 64; {t with c_gpr := holUpdate 7 (holUpdate 7 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((2147483648 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat), 7) (fixture s 0 2147483648 64) = _
  have numeric : (((2147483648 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_0_5_0
example (s : riscv_state) : «dfn'SLL» (0,1,2) (fixture s 0 4294967296 65) =
 (let t := fixture s 0 4294967296 65; t) := by
  change «write'GPR» (((4294967296 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat), 0) (fixture s 0 4294967296 65) = _
  have numeric : (((4294967296 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat)) = (8589934592 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_0_5_1
example (s : riscv_state) : «dfn'SLL» (1,1,2) (fixture s 0 4294967296 65) =
 (let t := fixture s 0 4294967296 65; {t with c_gpr := holUpdate 7 (holUpdate 1 8589934592 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((4294967296 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat), 1) (fixture s 0 4294967296 65) = _
  have numeric : (((4294967296 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat)) = (8589934592 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_0_5_2
example (s : riscv_state) : «dfn'SLL» (2,1,2) (fixture s 0 4294967296 65) =
 (let t := fixture s 0 4294967296 65; {t with c_gpr := holUpdate 7 (holUpdate 2 8589934592 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((4294967296 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat), 2) (fixture s 0 4294967296 65) = _
  have numeric : (((4294967296 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat)) = (8589934592 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_0_5_7
example (s : riscv_state) : «dfn'SLL» (7,1,2) (fixture s 0 4294967296 65) =
 (let t := fixture s 0 4294967296 65; {t with c_gpr := holUpdate 7 (holUpdate 7 8589934592 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((4294967296 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat), 7) (fixture s 0 4294967296 65) = _
  have numeric : (((4294967296 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat)) = (8589934592 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_0_6_0
example (s : riscv_state) : «dfn'SLL» (0,1,2) (fixture s 0 9223372036854775809 127) =
 (let t := fixture s 0 9223372036854775809 127; t) := by
  change «write'GPR» (((9223372036854775809 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat), 0) (fixture s 0 9223372036854775809 127) = _
  have numeric : (((9223372036854775809 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_0_6_1
example (s : riscv_state) : «dfn'SLL» (1,1,2) (fixture s 0 9223372036854775809 127) =
 (let t := fixture s 0 9223372036854775809 127; {t with c_gpr := holUpdate 7 (holUpdate 1 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775809 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat), 1) (fixture s 0 9223372036854775809 127) = _
  have numeric : (((9223372036854775809 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_0_6_2
example (s : riscv_state) : «dfn'SLL» (2,1,2) (fixture s 0 9223372036854775809 127) =
 (let t := fixture s 0 9223372036854775809 127; {t with c_gpr := holUpdate 7 (holUpdate 2 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775809 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat), 2) (fixture s 0 9223372036854775809 127) = _
  have numeric : (((9223372036854775809 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_0_6_7
example (s : riscv_state) : «dfn'SLL» (7,1,2) (fixture s 0 9223372036854775809 127) =
 (let t := fixture s 0 9223372036854775809 127; {t with c_gpr := holUpdate 7 (holUpdate 7 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775809 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat), 7) (fixture s 0 9223372036854775809 127) = _
  have numeric : (((9223372036854775809 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_0_7_0
example (s : riscv_state) : «dfn'SLL» (0,1,2) (fixture s 0 17 129) =
 (let t := fixture s 0 17 129; t) := by
  change «write'GPR» (((17 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat), 0) (fixture s 0 17 129) = _
  have numeric : (((17 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat)) = (34 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_0_7_1
example (s : riscv_state) : «dfn'SLL» (1,1,2) (fixture s 0 17 129) =
 (let t := fixture s 0 17 129; {t with c_gpr := holUpdate 7 (holUpdate 1 34 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((17 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat), 1) (fixture s 0 17 129) = _
  have numeric : (((17 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat)) = (34 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_0_7_2
example (s : riscv_state) : «dfn'SLL» (2,1,2) (fixture s 0 17 129) =
 (let t := fixture s 0 17 129; {t with c_gpr := holUpdate 7 (holUpdate 2 34 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((17 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat), 2) (fixture s 0 17 129) = _
  have numeric : (((17 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat)) = (34 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_0_7_7
example (s : riscv_state) : «dfn'SLL» (7,1,2) (fixture s 0 17 129) =
 (let t := fixture s 0 17 129; {t with c_gpr := holUpdate 7 (holUpdate 7 34 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((17 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat), 7) (fixture s 0 17 129) = _
  have numeric : (((17 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat)) = (34 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_0_8_0
example (s : riscv_state) : «dfn'SLL» (0,0,2) (fixture s 0 17 31) =
 (let t := fixture s 0 17 31; t) := by
  change «write'GPR» (((0 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 0) (fixture s 0 17 31) = _
  have numeric : (((0 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_0_8_1
example (s : riscv_state) : «dfn'SLL» (1,0,2) (fixture s 0 17 31) =
 (let t := fixture s 0 17 31; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((0 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 1) (fixture s 0 17 31) = _
  have numeric : (((0 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_0_8_2
example (s : riscv_state) : «dfn'SLL» (2,0,2) (fixture s 0 17 31) =
 (let t := fixture s 0 17 31; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((0 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 2) (fixture s 0 17 31) = _
  have numeric : (((0 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_0_8_7
example (s : riscv_state) : «dfn'SLL» (7,0,2) (fixture s 0 17 31) =
 (let t := fixture s 0 17 31; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((0 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 7) (fixture s 0 17 31) = _
  have numeric : (((0 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_0_9_0
example (s : riscv_state) : «dfn'SLL» (0,1,0) (fixture s 0 18446744073709551615 63) =
 (let t := fixture s 0 18446744073709551615 63; t) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 0) (fixture s 0 18446744073709551615 63) = _
  have numeric : (((18446744073709551615 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_0_9_1
example (s : riscv_state) : «dfn'SLL» (1,1,0) (fixture s 0 18446744073709551615 63) =
 (let t := fixture s 0 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 1) (fixture s 0 18446744073709551615 63) = _
  have numeric : (((18446744073709551615 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_0_9_2
example (s : riscv_state) : «dfn'SLL» (2,1,0) (fixture s 0 18446744073709551615 63) =
 (let t := fixture s 0 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 2) (fixture s 0 18446744073709551615 63) = _
  have numeric : (((18446744073709551615 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_0_9_7
example (s : riscv_state) : «dfn'SLL» (7,1,0) (fixture s 0 18446744073709551615 63) =
 (let t := fixture s 0 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 7) (fixture s 0 18446744073709551615 63) = _
  have numeric : (((18446744073709551615 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_2_0_0
example (s : riscv_state) : «dfn'SLL» (0,1,2) (fixture s 2 9223372036854775808 0) =
 (let t := fixture s 2 9223372036854775808 0; t) := by
  change «write'GPR» (((9223372036854775808 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat), 0) (fixture s 2 9223372036854775808 0) = _
  have numeric : (((9223372036854775808 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_2_0_1
example (s : riscv_state) : «dfn'SLL» (1,1,2) (fixture s 2 9223372036854775808 0) =
 (let t := fixture s 2 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 1 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775808 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat), 1) (fixture s 2 9223372036854775808 0) = _
  have numeric : (((9223372036854775808 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_2_0_2
example (s : riscv_state) : «dfn'SLL» (2,1,2) (fixture s 2 9223372036854775808 0) =
 (let t := fixture s 2 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 2 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775808 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat), 2) (fixture s 2 9223372036854775808 0) = _
  have numeric : (((9223372036854775808 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_2_0_7
example (s : riscv_state) : «dfn'SLL» (7,1,2) (fixture s 2 9223372036854775808 0) =
 (let t := fixture s 2 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 7 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775808 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat), 7) (fixture s 2 9223372036854775808 0) = _
  have numeric : (((9223372036854775808 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_2_1_0
example (s : riscv_state) : «dfn'SLL» (0,1,2) (fixture s 2 2147483649 31) =
 (let t := fixture s 2 2147483649 31; t) := by
  change «write'GPR» (((2147483649 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat), 0) (fixture s 2 2147483649 31) = _
  have numeric : (((2147483649 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat)) = (4611686020574871552 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_2_1_1
example (s : riscv_state) : «dfn'SLL» (1,1,2) (fixture s 2 2147483649 31) =
 (let t := fixture s 2 2147483649 31; {t with c_gpr := holUpdate 7 (holUpdate 1 4611686020574871552 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((2147483649 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat), 1) (fixture s 2 2147483649 31) = _
  have numeric : (((2147483649 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat)) = (4611686020574871552 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_2_1_2
example (s : riscv_state) : «dfn'SLL» (2,1,2) (fixture s 2 2147483649 31) =
 (let t := fixture s 2 2147483649 31; {t with c_gpr := holUpdate 7 (holUpdate 2 4611686020574871552 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((2147483649 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat), 2) (fixture s 2 2147483649 31) = _
  have numeric : (((2147483649 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat)) = (4611686020574871552 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_2_1_7
example (s : riscv_state) : «dfn'SLL» (7,1,2) (fixture s 2 2147483649 31) =
 (let t := fixture s 2 2147483649 31; {t with c_gpr := holUpdate 7 (holUpdate 7 4611686020574871552 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((2147483649 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat), 7) (fixture s 2 2147483649 31) = _
  have numeric : (((2147483649 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat)) = (4611686020574871552 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_2_2_0
example (s : riscv_state) : «dfn'SLL» (0,1,2) (fixture s 2 4294967297 32) =
 (let t := fixture s 2 4294967297 32; t) := by
  change «write'GPR» (((4294967297 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (32 : BitVec 64))).toNat), 0) (fixture s 2 4294967297 32) = _
  have numeric : (((4294967297 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (32 : BitVec 64))).toNat)) = (4294967296 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_2_2_1
example (s : riscv_state) : «dfn'SLL» (1,1,2) (fixture s 2 4294967297 32) =
 (let t := fixture s 2 4294967297 32; {t with c_gpr := holUpdate 7 (holUpdate 1 4294967296 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((4294967297 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (32 : BitVec 64))).toNat), 1) (fixture s 2 4294967297 32) = _
  have numeric : (((4294967297 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (32 : BitVec 64))).toNat)) = (4294967296 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_2_2_2
example (s : riscv_state) : «dfn'SLL» (2,1,2) (fixture s 2 4294967297 32) =
 (let t := fixture s 2 4294967297 32; {t with c_gpr := holUpdate 7 (holUpdate 2 4294967296 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((4294967297 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (32 : BitVec 64))).toNat), 2) (fixture s 2 4294967297 32) = _
  have numeric : (((4294967297 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (32 : BitVec 64))).toNat)) = (4294967296 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_2_2_7
example (s : riscv_state) : «dfn'SLL» (7,1,2) (fixture s 2 4294967297 32) =
 (let t := fixture s 2 4294967297 32; {t with c_gpr := holUpdate 7 (holUpdate 7 4294967296 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((4294967297 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (32 : BitVec 64))).toNat), 7) (fixture s 2 4294967297 32) = _
  have numeric : (((4294967297 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (32 : BitVec 64))).toNat)) = (4294967296 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_2_3_0
example (s : riscv_state) : «dfn'SLL» (0,1,2) (fixture s 2 18446744073709551615 63) =
 (let t := fixture s 2 18446744073709551615 63; t) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (63 : BitVec 64))).toNat), 0) (fixture s 2 18446744073709551615 63) = _
  have numeric : (((18446744073709551615 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (63 : BitVec 64))).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_2_3_1
example (s : riscv_state) : «dfn'SLL» (1,1,2) (fixture s 2 18446744073709551615 63) =
 (let t := fixture s 2 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 1 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (63 : BitVec 64))).toNat), 1) (fixture s 2 18446744073709551615 63) = _
  have numeric : (((18446744073709551615 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (63 : BitVec 64))).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_2_3_2
example (s : riscv_state) : «dfn'SLL» (2,1,2) (fixture s 2 18446744073709551615 63) =
 (let t := fixture s 2 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 2 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (63 : BitVec 64))).toNat), 2) (fixture s 2 18446744073709551615 63) = _
  have numeric : (((18446744073709551615 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (63 : BitVec 64))).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_2_3_7
example (s : riscv_state) : «dfn'SLL» (7,1,2) (fixture s 2 18446744073709551615 63) =
 (let t := fixture s 2 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 7 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (63 : BitVec 64))).toNat), 7) (fixture s 2 18446744073709551615 63) = _
  have numeric : (((18446744073709551615 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (63 : BitVec 64))).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_2_4_0
example (s : riscv_state) : «dfn'SLL» (0,1,2) (fixture s 2 2147483648 64) =
 (let t := fixture s 2 2147483648 64; t) := by
  change «write'GPR» (((2147483648 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (64 : BitVec 64))).toNat), 0) (fixture s 2 2147483648 64) = _
  have numeric : (((2147483648 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (64 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_2_4_1
example (s : riscv_state) : «dfn'SLL» (1,1,2) (fixture s 2 2147483648 64) =
 (let t := fixture s 2 2147483648 64; {t with c_gpr := holUpdate 7 (holUpdate 1 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((2147483648 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (64 : BitVec 64))).toNat), 1) (fixture s 2 2147483648 64) = _
  have numeric : (((2147483648 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (64 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_2_4_2
example (s : riscv_state) : «dfn'SLL» (2,1,2) (fixture s 2 2147483648 64) =
 (let t := fixture s 2 2147483648 64; {t with c_gpr := holUpdate 7 (holUpdate 2 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((2147483648 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (64 : BitVec 64))).toNat), 2) (fixture s 2 2147483648 64) = _
  have numeric : (((2147483648 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (64 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_2_4_7
example (s : riscv_state) : «dfn'SLL» (7,1,2) (fixture s 2 2147483648 64) =
 (let t := fixture s 2 2147483648 64; {t with c_gpr := holUpdate 7 (holUpdate 7 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((2147483648 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (64 : BitVec 64))).toNat), 7) (fixture s 2 2147483648 64) = _
  have numeric : (((2147483648 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (64 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_2_5_0
example (s : riscv_state) : «dfn'SLL» (0,1,2) (fixture s 2 4294967296 65) =
 (let t := fixture s 2 4294967296 65; t) := by
  change «write'GPR» (((4294967296 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (65 : BitVec 64))).toNat), 0) (fixture s 2 4294967296 65) = _
  have numeric : (((4294967296 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (65 : BitVec 64))).toNat)) = (8589934592 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_2_5_1
example (s : riscv_state) : «dfn'SLL» (1,1,2) (fixture s 2 4294967296 65) =
 (let t := fixture s 2 4294967296 65; {t with c_gpr := holUpdate 7 (holUpdate 1 8589934592 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((4294967296 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (65 : BitVec 64))).toNat), 1) (fixture s 2 4294967296 65) = _
  have numeric : (((4294967296 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (65 : BitVec 64))).toNat)) = (8589934592 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_2_5_2
example (s : riscv_state) : «dfn'SLL» (2,1,2) (fixture s 2 4294967296 65) =
 (let t := fixture s 2 4294967296 65; {t with c_gpr := holUpdate 7 (holUpdate 2 8589934592 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((4294967296 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (65 : BitVec 64))).toNat), 2) (fixture s 2 4294967296 65) = _
  have numeric : (((4294967296 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (65 : BitVec 64))).toNat)) = (8589934592 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_2_5_7
example (s : riscv_state) : «dfn'SLL» (7,1,2) (fixture s 2 4294967296 65) =
 (let t := fixture s 2 4294967296 65; {t with c_gpr := holUpdate 7 (holUpdate 7 8589934592 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((4294967296 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (65 : BitVec 64))).toNat), 7) (fixture s 2 4294967296 65) = _
  have numeric : (((4294967296 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (65 : BitVec 64))).toNat)) = (8589934592 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_2_6_0
example (s : riscv_state) : «dfn'SLL» (0,1,2) (fixture s 2 9223372036854775809 127) =
 (let t := fixture s 2 9223372036854775809 127; t) := by
  change «write'GPR» (((9223372036854775809 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (127 : BitVec 64))).toNat), 0) (fixture s 2 9223372036854775809 127) = _
  have numeric : (((9223372036854775809 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (127 : BitVec 64))).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_2_6_1
example (s : riscv_state) : «dfn'SLL» (1,1,2) (fixture s 2 9223372036854775809 127) =
 (let t := fixture s 2 9223372036854775809 127; {t with c_gpr := holUpdate 7 (holUpdate 1 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775809 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (127 : BitVec 64))).toNat), 1) (fixture s 2 9223372036854775809 127) = _
  have numeric : (((9223372036854775809 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (127 : BitVec 64))).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_2_6_2
example (s : riscv_state) : «dfn'SLL» (2,1,2) (fixture s 2 9223372036854775809 127) =
 (let t := fixture s 2 9223372036854775809 127; {t with c_gpr := holUpdate 7 (holUpdate 2 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775809 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (127 : BitVec 64))).toNat), 2) (fixture s 2 9223372036854775809 127) = _
  have numeric : (((9223372036854775809 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (127 : BitVec 64))).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_2_6_7
example (s : riscv_state) : «dfn'SLL» (7,1,2) (fixture s 2 9223372036854775809 127) =
 (let t := fixture s 2 9223372036854775809 127; {t with c_gpr := holUpdate 7 (holUpdate 7 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775809 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (127 : BitVec 64))).toNat), 7) (fixture s 2 9223372036854775809 127) = _
  have numeric : (((9223372036854775809 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (127 : BitVec 64))).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_2_7_0
example (s : riscv_state) : «dfn'SLL» (0,1,2) (fixture s 2 17 129) =
 (let t := fixture s 2 17 129; t) := by
  change «write'GPR» (((17 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (129 : BitVec 64))).toNat), 0) (fixture s 2 17 129) = _
  have numeric : (((17 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (129 : BitVec 64))).toNat)) = (34 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_2_7_1
example (s : riscv_state) : «dfn'SLL» (1,1,2) (fixture s 2 17 129) =
 (let t := fixture s 2 17 129; {t with c_gpr := holUpdate 7 (holUpdate 1 34 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((17 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (129 : BitVec 64))).toNat), 1) (fixture s 2 17 129) = _
  have numeric : (((17 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (129 : BitVec 64))).toNat)) = (34 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_2_7_2
example (s : riscv_state) : «dfn'SLL» (2,1,2) (fixture s 2 17 129) =
 (let t := fixture s 2 17 129; {t with c_gpr := holUpdate 7 (holUpdate 2 34 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((17 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (129 : BitVec 64))).toNat), 2) (fixture s 2 17 129) = _
  have numeric : (((17 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (129 : BitVec 64))).toNat)) = (34 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_2_7_7
example (s : riscv_state) : «dfn'SLL» (7,1,2) (fixture s 2 17 129) =
 (let t := fixture s 2 17 129; {t with c_gpr := holUpdate 7 (holUpdate 7 34 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((17 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (129 : BitVec 64))).toNat), 7) (fixture s 2 17 129) = _
  have numeric : (((17 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (129 : BitVec 64))).toNat)) = (34 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_2_8_0
example (s : riscv_state) : «dfn'SLL» (0,0,2) (fixture s 2 17 31) =
 (let t := fixture s 2 17 31; t) := by
  change «write'GPR» (((0 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat), 0) (fixture s 2 17 31) = _
  have numeric : (((0 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_2_8_1
example (s : riscv_state) : «dfn'SLL» (1,0,2) (fixture s 2 17 31) =
 (let t := fixture s 2 17 31; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((0 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat), 1) (fixture s 2 17 31) = _
  have numeric : (((0 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_2_8_2
example (s : riscv_state) : «dfn'SLL» (2,0,2) (fixture s 2 17 31) =
 (let t := fixture s 2 17 31; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((0 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat), 2) (fixture s 2 17 31) = _
  have numeric : (((0 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_2_8_7
example (s : riscv_state) : «dfn'SLL» (7,0,2) (fixture s 2 17 31) =
 (let t := fixture s 2 17 31; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((0 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat), 7) (fixture s 2 17 31) = _
  have numeric : (((0 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_2_9_0
example (s : riscv_state) : «dfn'SLL» (0,1,0) (fixture s 2 18446744073709551615 63) =
 (let t := fixture s 2 18446744073709551615 63; t) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat), 0) (fixture s 2 18446744073709551615 63) = _
  have numeric : (((18446744073709551615 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_2_9_1
example (s : riscv_state) : «dfn'SLL» (1,1,0) (fixture s 2 18446744073709551615 63) =
 (let t := fixture s 2 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat), 1) (fixture s 2 18446744073709551615 63) = _
  have numeric : (((18446744073709551615 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_2_9_2
example (s : riscv_state) : «dfn'SLL» (2,1,0) (fixture s 2 18446744073709551615 63) =
 (let t := fixture s 2 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat), 2) (fixture s 2 18446744073709551615 63) = _
  have numeric : (((18446744073709551615 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_2_9_7
example (s : riscv_state) : «dfn'SLL» (7,1,0) (fixture s 2 18446744073709551615 63) =
 (let t := fixture s 2 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat), 7) (fixture s 2 18446744073709551615 63) = _
  have numeric : (((18446744073709551615 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_3_0_0
example (s : riscv_state) : «dfn'SLL» (0,1,2) (fixture s 3 9223372036854775808 0) =
 (let t := fixture s 3 9223372036854775808 0; t) := by
  change «write'GPR» (((9223372036854775808 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat), 0) (fixture s 3 9223372036854775808 0) = _
  have numeric : (((9223372036854775808 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_3_0_1
example (s : riscv_state) : «dfn'SLL» (1,1,2) (fixture s 3 9223372036854775808 0) =
 (let t := fixture s 3 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 1 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775808 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat), 1) (fixture s 3 9223372036854775808 0) = _
  have numeric : (((9223372036854775808 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_3_0_2
example (s : riscv_state) : «dfn'SLL» (2,1,2) (fixture s 3 9223372036854775808 0) =
 (let t := fixture s 3 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 2 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775808 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat), 2) (fixture s 3 9223372036854775808 0) = _
  have numeric : (((9223372036854775808 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_3_0_7
example (s : riscv_state) : «dfn'SLL» (7,1,2) (fixture s 3 9223372036854775808 0) =
 (let t := fixture s 3 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 7 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775808 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat), 7) (fixture s 3 9223372036854775808 0) = _
  have numeric : (((9223372036854775808 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_3_1_0
example (s : riscv_state) : «dfn'SLL» (0,1,2) (fixture s 3 2147483649 31) =
 (let t := fixture s 3 2147483649 31; t) := by
  change «write'GPR» (((2147483649 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat), 0) (fixture s 3 2147483649 31) = _
  have numeric : (((2147483649 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat)) = (4611686020574871552 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_3_1_1
example (s : riscv_state) : «dfn'SLL» (1,1,2) (fixture s 3 2147483649 31) =
 (let t := fixture s 3 2147483649 31; {t with c_gpr := holUpdate 7 (holUpdate 1 4611686020574871552 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((2147483649 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat), 1) (fixture s 3 2147483649 31) = _
  have numeric : (((2147483649 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat)) = (4611686020574871552 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_3_1_2
example (s : riscv_state) : «dfn'SLL» (2,1,2) (fixture s 3 2147483649 31) =
 (let t := fixture s 3 2147483649 31; {t with c_gpr := holUpdate 7 (holUpdate 2 4611686020574871552 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((2147483649 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat), 2) (fixture s 3 2147483649 31) = _
  have numeric : (((2147483649 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat)) = (4611686020574871552 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_3_1_7
example (s : riscv_state) : «dfn'SLL» (7,1,2) (fixture s 3 2147483649 31) =
 (let t := fixture s 3 2147483649 31; {t with c_gpr := holUpdate 7 (holUpdate 7 4611686020574871552 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((2147483649 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat), 7) (fixture s 3 2147483649 31) = _
  have numeric : (((2147483649 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat)) = (4611686020574871552 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_3_2_0
example (s : riscv_state) : «dfn'SLL» (0,1,2) (fixture s 3 4294967297 32) =
 (let t := fixture s 3 4294967297 32; t) := by
  change «write'GPR» (((4294967297 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (32 : BitVec 64))).toNat), 0) (fixture s 3 4294967297 32) = _
  have numeric : (((4294967297 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (32 : BitVec 64))).toNat)) = (4294967296 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_3_2_1
example (s : riscv_state) : «dfn'SLL» (1,1,2) (fixture s 3 4294967297 32) =
 (let t := fixture s 3 4294967297 32; {t with c_gpr := holUpdate 7 (holUpdate 1 4294967296 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((4294967297 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (32 : BitVec 64))).toNat), 1) (fixture s 3 4294967297 32) = _
  have numeric : (((4294967297 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (32 : BitVec 64))).toNat)) = (4294967296 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_3_2_2
example (s : riscv_state) : «dfn'SLL» (2,1,2) (fixture s 3 4294967297 32) =
 (let t := fixture s 3 4294967297 32; {t with c_gpr := holUpdate 7 (holUpdate 2 4294967296 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((4294967297 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (32 : BitVec 64))).toNat), 2) (fixture s 3 4294967297 32) = _
  have numeric : (((4294967297 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (32 : BitVec 64))).toNat)) = (4294967296 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_3_2_7
example (s : riscv_state) : «dfn'SLL» (7,1,2) (fixture s 3 4294967297 32) =
 (let t := fixture s 3 4294967297 32; {t with c_gpr := holUpdate 7 (holUpdate 7 4294967296 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((4294967297 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (32 : BitVec 64))).toNat), 7) (fixture s 3 4294967297 32) = _
  have numeric : (((4294967297 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (32 : BitVec 64))).toNat)) = (4294967296 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_3_3_0
example (s : riscv_state) : «dfn'SLL» (0,1,2) (fixture s 3 18446744073709551615 63) =
 (let t := fixture s 3 18446744073709551615 63; t) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (63 : BitVec 64))).toNat), 0) (fixture s 3 18446744073709551615 63) = _
  have numeric : (((18446744073709551615 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (63 : BitVec 64))).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_3_3_1
example (s : riscv_state) : «dfn'SLL» (1,1,2) (fixture s 3 18446744073709551615 63) =
 (let t := fixture s 3 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 1 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (63 : BitVec 64))).toNat), 1) (fixture s 3 18446744073709551615 63) = _
  have numeric : (((18446744073709551615 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (63 : BitVec 64))).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_3_3_2
example (s : riscv_state) : «dfn'SLL» (2,1,2) (fixture s 3 18446744073709551615 63) =
 (let t := fixture s 3 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 2 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (63 : BitVec 64))).toNat), 2) (fixture s 3 18446744073709551615 63) = _
  have numeric : (((18446744073709551615 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (63 : BitVec 64))).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_3_3_7
example (s : riscv_state) : «dfn'SLL» (7,1,2) (fixture s 3 18446744073709551615 63) =
 (let t := fixture s 3 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 7 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (63 : BitVec 64))).toNat), 7) (fixture s 3 18446744073709551615 63) = _
  have numeric : (((18446744073709551615 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (63 : BitVec 64))).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_3_4_0
example (s : riscv_state) : «dfn'SLL» (0,1,2) (fixture s 3 2147483648 64) =
 (let t := fixture s 3 2147483648 64; t) := by
  change «write'GPR» (((2147483648 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (64 : BitVec 64))).toNat), 0) (fixture s 3 2147483648 64) = _
  have numeric : (((2147483648 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (64 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_3_4_1
example (s : riscv_state) : «dfn'SLL» (1,1,2) (fixture s 3 2147483648 64) =
 (let t := fixture s 3 2147483648 64; {t with c_gpr := holUpdate 7 (holUpdate 1 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((2147483648 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (64 : BitVec 64))).toNat), 1) (fixture s 3 2147483648 64) = _
  have numeric : (((2147483648 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (64 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_3_4_2
example (s : riscv_state) : «dfn'SLL» (2,1,2) (fixture s 3 2147483648 64) =
 (let t := fixture s 3 2147483648 64; {t with c_gpr := holUpdate 7 (holUpdate 2 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((2147483648 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (64 : BitVec 64))).toNat), 2) (fixture s 3 2147483648 64) = _
  have numeric : (((2147483648 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (64 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_3_4_7
example (s : riscv_state) : «dfn'SLL» (7,1,2) (fixture s 3 2147483648 64) =
 (let t := fixture s 3 2147483648 64; {t with c_gpr := holUpdate 7 (holUpdate 7 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((2147483648 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (64 : BitVec 64))).toNat), 7) (fixture s 3 2147483648 64) = _
  have numeric : (((2147483648 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (64 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_3_5_0
example (s : riscv_state) : «dfn'SLL» (0,1,2) (fixture s 3 4294967296 65) =
 (let t := fixture s 3 4294967296 65; t) := by
  change «write'GPR» (((4294967296 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (65 : BitVec 64))).toNat), 0) (fixture s 3 4294967296 65) = _
  have numeric : (((4294967296 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (65 : BitVec 64))).toNat)) = (8589934592 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_3_5_1
example (s : riscv_state) : «dfn'SLL» (1,1,2) (fixture s 3 4294967296 65) =
 (let t := fixture s 3 4294967296 65; {t with c_gpr := holUpdate 7 (holUpdate 1 8589934592 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((4294967296 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (65 : BitVec 64))).toNat), 1) (fixture s 3 4294967296 65) = _
  have numeric : (((4294967296 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (65 : BitVec 64))).toNat)) = (8589934592 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_3_5_2
example (s : riscv_state) : «dfn'SLL» (2,1,2) (fixture s 3 4294967296 65) =
 (let t := fixture s 3 4294967296 65; {t with c_gpr := holUpdate 7 (holUpdate 2 8589934592 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((4294967296 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (65 : BitVec 64))).toNat), 2) (fixture s 3 4294967296 65) = _
  have numeric : (((4294967296 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (65 : BitVec 64))).toNat)) = (8589934592 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_3_5_7
example (s : riscv_state) : «dfn'SLL» (7,1,2) (fixture s 3 4294967296 65) =
 (let t := fixture s 3 4294967296 65; {t with c_gpr := holUpdate 7 (holUpdate 7 8589934592 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((4294967296 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (65 : BitVec 64))).toNat), 7) (fixture s 3 4294967296 65) = _
  have numeric : (((4294967296 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (65 : BitVec 64))).toNat)) = (8589934592 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_3_6_0
example (s : riscv_state) : «dfn'SLL» (0,1,2) (fixture s 3 9223372036854775809 127) =
 (let t := fixture s 3 9223372036854775809 127; t) := by
  change «write'GPR» (((9223372036854775809 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (127 : BitVec 64))).toNat), 0) (fixture s 3 9223372036854775809 127) = _
  have numeric : (((9223372036854775809 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (127 : BitVec 64))).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_3_6_1
example (s : riscv_state) : «dfn'SLL» (1,1,2) (fixture s 3 9223372036854775809 127) =
 (let t := fixture s 3 9223372036854775809 127; {t with c_gpr := holUpdate 7 (holUpdate 1 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775809 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (127 : BitVec 64))).toNat), 1) (fixture s 3 9223372036854775809 127) = _
  have numeric : (((9223372036854775809 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (127 : BitVec 64))).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_3_6_2
example (s : riscv_state) : «dfn'SLL» (2,1,2) (fixture s 3 9223372036854775809 127) =
 (let t := fixture s 3 9223372036854775809 127; {t with c_gpr := holUpdate 7 (holUpdate 2 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775809 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (127 : BitVec 64))).toNat), 2) (fixture s 3 9223372036854775809 127) = _
  have numeric : (((9223372036854775809 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (127 : BitVec 64))).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_3_6_7
example (s : riscv_state) : «dfn'SLL» (7,1,2) (fixture s 3 9223372036854775809 127) =
 (let t := fixture s 3 9223372036854775809 127; {t with c_gpr := holUpdate 7 (holUpdate 7 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775809 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (127 : BitVec 64))).toNat), 7) (fixture s 3 9223372036854775809 127) = _
  have numeric : (((9223372036854775809 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (127 : BitVec 64))).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_3_7_0
example (s : riscv_state) : «dfn'SLL» (0,1,2) (fixture s 3 17 129) =
 (let t := fixture s 3 17 129; t) := by
  change «write'GPR» (((17 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (129 : BitVec 64))).toNat), 0) (fixture s 3 17 129) = _
  have numeric : (((17 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (129 : BitVec 64))).toNat)) = (34 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_3_7_1
example (s : riscv_state) : «dfn'SLL» (1,1,2) (fixture s 3 17 129) =
 (let t := fixture s 3 17 129; {t with c_gpr := holUpdate 7 (holUpdate 1 34 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((17 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (129 : BitVec 64))).toNat), 1) (fixture s 3 17 129) = _
  have numeric : (((17 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (129 : BitVec 64))).toNat)) = (34 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_3_7_2
example (s : riscv_state) : «dfn'SLL» (2,1,2) (fixture s 3 17 129) =
 (let t := fixture s 3 17 129; {t with c_gpr := holUpdate 7 (holUpdate 2 34 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((17 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (129 : BitVec 64))).toNat), 2) (fixture s 3 17 129) = _
  have numeric : (((17 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (129 : BitVec 64))).toNat)) = (34 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_3_7_7
example (s : riscv_state) : «dfn'SLL» (7,1,2) (fixture s 3 17 129) =
 (let t := fixture s 3 17 129; {t with c_gpr := holUpdate 7 (holUpdate 7 34 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((17 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (129 : BitVec 64))).toNat), 7) (fixture s 3 17 129) = _
  have numeric : (((17 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (129 : BitVec 64))).toNat)) = (34 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_3_8_0
example (s : riscv_state) : «dfn'SLL» (0,0,2) (fixture s 3 17 31) =
 (let t := fixture s 3 17 31; t) := by
  change «write'GPR» (((0 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat), 0) (fixture s 3 17 31) = _
  have numeric : (((0 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_3_8_1
example (s : riscv_state) : «dfn'SLL» (1,0,2) (fixture s 3 17 31) =
 (let t := fixture s 3 17 31; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((0 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat), 1) (fixture s 3 17 31) = _
  have numeric : (((0 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_3_8_2
example (s : riscv_state) : «dfn'SLL» (2,0,2) (fixture s 3 17 31) =
 (let t := fixture s 3 17 31; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((0 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat), 2) (fixture s 3 17 31) = _
  have numeric : (((0 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_3_8_7
example (s : riscv_state) : «dfn'SLL» (7,0,2) (fixture s 3 17 31) =
 (let t := fixture s 3 17 31; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((0 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat), 7) (fixture s 3 17 31) = _
  have numeric : (((0 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_3_9_0
example (s : riscv_state) : «dfn'SLL» (0,1,0) (fixture s 3 18446744073709551615 63) =
 (let t := fixture s 3 18446744073709551615 63; t) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat), 0) (fixture s 3 18446744073709551615 63) = _
  have numeric : (((18446744073709551615 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_3_9_1
example (s : riscv_state) : «dfn'SLL» (1,1,0) (fixture s 3 18446744073709551615 63) =
 (let t := fixture s 3 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat), 1) (fixture s 3 18446744073709551615 63) = _
  have numeric : (((18446744073709551615 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_3_9_2
example (s : riscv_state) : «dfn'SLL» (2,1,0) (fixture s 3 18446744073709551615 63) =
 (let t := fixture s 3 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat), 2) (fixture s 3 18446744073709551615 63) = _
  have numeric : (((18446744073709551615 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLL_3_9_7
example (s : riscv_state) : «dfn'SLL» (7,1,0) (fixture s 3 18446744073709551615 63) =
 (let t := fixture s 3 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat), 7) (fixture s 3 18446744073709551615 63) = _
  have numeric : (((18446744073709551615 : BitVec 64) <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_0_0_0
example (s : riscv_state) : «dfn'SLLW» (0,1,2) (fixture s 0 9223372036854775808 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775808 0) := by rfl

-- register_shift_SLLW_0_0_1
example (s : riscv_state) : «dfn'SLLW» (1,1,2) (fixture s 0 9223372036854775808 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775808 0) := by rfl

-- register_shift_SLLW_0_0_2
example (s : riscv_state) : «dfn'SLLW» (2,1,2) (fixture s 0 9223372036854775808 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775808 0) := by rfl

-- register_shift_SLLW_0_0_7
example (s : riscv_state) : «dfn'SLLW» (7,1,2) (fixture s 0 9223372036854775808 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775808 0) := by rfl

-- register_shift_SLLW_0_1_0
example (s : riscv_state) : «dfn'SLLW» (0,1,2) (fixture s 0 2147483649 31) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483649 31) := by rfl

-- register_shift_SLLW_0_1_1
example (s : riscv_state) : «dfn'SLLW» (1,1,2) (fixture s 0 2147483649 31) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483649 31) := by rfl

-- register_shift_SLLW_0_1_2
example (s : riscv_state) : «dfn'SLLW» (2,1,2) (fixture s 0 2147483649 31) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483649 31) := by rfl

-- register_shift_SLLW_0_1_7
example (s : riscv_state) : «dfn'SLLW» (7,1,2) (fixture s 0 2147483649 31) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483649 31) := by rfl

-- register_shift_SLLW_0_2_0
example (s : riscv_state) : «dfn'SLLW» (0,1,2) (fixture s 0 4294967297 32) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967297 32) := by rfl

-- register_shift_SLLW_0_2_1
example (s : riscv_state) : «dfn'SLLW» (1,1,2) (fixture s 0 4294967297 32) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967297 32) := by rfl

-- register_shift_SLLW_0_2_2
example (s : riscv_state) : «dfn'SLLW» (2,1,2) (fixture s 0 4294967297 32) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967297 32) := by rfl

-- register_shift_SLLW_0_2_7
example (s : riscv_state) : «dfn'SLLW» (7,1,2) (fixture s 0 4294967297 32) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967297 32) := by rfl

-- register_shift_SLLW_0_3_0
example (s : riscv_state) : «dfn'SLLW» (0,1,2) (fixture s 0 18446744073709551615 63) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 63) := by rfl

-- register_shift_SLLW_0_3_1
example (s : riscv_state) : «dfn'SLLW» (1,1,2) (fixture s 0 18446744073709551615 63) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 63) := by rfl

-- register_shift_SLLW_0_3_2
example (s : riscv_state) : «dfn'SLLW» (2,1,2) (fixture s 0 18446744073709551615 63) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 63) := by rfl

-- register_shift_SLLW_0_3_7
example (s : riscv_state) : «dfn'SLLW» (7,1,2) (fixture s 0 18446744073709551615 63) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 63) := by rfl

-- register_shift_SLLW_0_4_0
example (s : riscv_state) : «dfn'SLLW» (0,1,2) (fixture s 0 2147483648 64) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483648 64) := by rfl

-- register_shift_SLLW_0_4_1
example (s : riscv_state) : «dfn'SLLW» (1,1,2) (fixture s 0 2147483648 64) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483648 64) := by rfl

-- register_shift_SLLW_0_4_2
example (s : riscv_state) : «dfn'SLLW» (2,1,2) (fixture s 0 2147483648 64) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483648 64) := by rfl

-- register_shift_SLLW_0_4_7
example (s : riscv_state) : «dfn'SLLW» (7,1,2) (fixture s 0 2147483648 64) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483648 64) := by rfl

-- register_shift_SLLW_0_5_0
example (s : riscv_state) : «dfn'SLLW» (0,1,2) (fixture s 0 4294967296 65) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967296 65) := by rfl

-- register_shift_SLLW_0_5_1
example (s : riscv_state) : «dfn'SLLW» (1,1,2) (fixture s 0 4294967296 65) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967296 65) := by rfl

-- register_shift_SLLW_0_5_2
example (s : riscv_state) : «dfn'SLLW» (2,1,2) (fixture s 0 4294967296 65) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967296 65) := by rfl

-- register_shift_SLLW_0_5_7
example (s : riscv_state) : «dfn'SLLW» (7,1,2) (fixture s 0 4294967296 65) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967296 65) := by rfl

-- register_shift_SLLW_0_6_0
example (s : riscv_state) : «dfn'SLLW» (0,1,2) (fixture s 0 9223372036854775809 127) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775809 127) := by rfl

-- register_shift_SLLW_0_6_1
example (s : riscv_state) : «dfn'SLLW» (1,1,2) (fixture s 0 9223372036854775809 127) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775809 127) := by rfl

-- register_shift_SLLW_0_6_2
example (s : riscv_state) : «dfn'SLLW» (2,1,2) (fixture s 0 9223372036854775809 127) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775809 127) := by rfl

-- register_shift_SLLW_0_6_7
example (s : riscv_state) : «dfn'SLLW» (7,1,2) (fixture s 0 9223372036854775809 127) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775809 127) := by rfl

-- register_shift_SLLW_0_7_0
example (s : riscv_state) : «dfn'SLLW» (0,1,2) (fixture s 0 17 129) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 129) := by rfl

-- register_shift_SLLW_0_7_1
example (s : riscv_state) : «dfn'SLLW» (1,1,2) (fixture s 0 17 129) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 129) := by rfl

-- register_shift_SLLW_0_7_2
example (s : riscv_state) : «dfn'SLLW» (2,1,2) (fixture s 0 17 129) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 129) := by rfl

-- register_shift_SLLW_0_7_7
example (s : riscv_state) : «dfn'SLLW» (7,1,2) (fixture s 0 17 129) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 129) := by rfl

-- register_shift_SLLW_0_8_0
example (s : riscv_state) : «dfn'SLLW» (0,0,2) (fixture s 0 17 31) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 31) := by rfl

-- register_shift_SLLW_0_8_1
example (s : riscv_state) : «dfn'SLLW» (1,0,2) (fixture s 0 17 31) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 31) := by rfl

-- register_shift_SLLW_0_8_2
example (s : riscv_state) : «dfn'SLLW» (2,0,2) (fixture s 0 17 31) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 31) := by rfl

-- register_shift_SLLW_0_8_7
example (s : riscv_state) : «dfn'SLLW» (7,0,2) (fixture s 0 17 31) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 31) := by rfl

-- register_shift_SLLW_0_9_0
example (s : riscv_state) : «dfn'SLLW» (0,1,0) (fixture s 0 18446744073709551615 63) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 63) := by rfl

-- register_shift_SLLW_0_9_1
example (s : riscv_state) : «dfn'SLLW» (1,1,0) (fixture s 0 18446744073709551615 63) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 63) := by rfl

-- register_shift_SLLW_0_9_2
example (s : riscv_state) : «dfn'SLLW» (2,1,0) (fixture s 0 18446744073709551615 63) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 63) := by rfl

-- register_shift_SLLW_0_9_7
example (s : riscv_state) : «dfn'SLLW» (7,1,0) (fixture s 0 18446744073709551615 63) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 63) := by rfl

-- register_shift_SLLW_2_0_0
example (s : riscv_state) : «dfn'SLLW» (0,1,2) (fixture s 2 9223372036854775808 0) =
 (let t := fixture s 2 9223372036854775808 0; t) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 0) (fixture s 2 9223372036854775808 0) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_2_0_1
example (s : riscv_state) : «dfn'SLLW» (1,1,2) (fixture s 2 9223372036854775808 0) =
 (let t := fixture s 2 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 1) (fixture s 2 9223372036854775808 0) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_2_0_2
example (s : riscv_state) : «dfn'SLLW» (2,1,2) (fixture s 2 9223372036854775808 0) =
 (let t := fixture s 2 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 2) (fixture s 2 9223372036854775808 0) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_2_0_7
example (s : riscv_state) : «dfn'SLLW» (7,1,2) (fixture s 2 9223372036854775808 0) =
 (let t := fixture s 2 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 7) (fixture s 2 9223372036854775808 0) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_2_1_0
example (s : riscv_state) : «dfn'SLLW» (0,1,2) (fixture s 2 2147483649 31) =
 (let t := fixture s 2 2147483649 31; t) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483649 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 0) (fixture s 2 2147483649 31) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483649 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_2_1_1
example (s : riscv_state) : «dfn'SLLW» (1,1,2) (fixture s 2 2147483649 31) =
 (let t := fixture s 2 2147483649 31; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483649 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 1) (fixture s 2 2147483649 31) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483649 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_2_1_2
example (s : riscv_state) : «dfn'SLLW» (2,1,2) (fixture s 2 2147483649 31) =
 (let t := fixture s 2 2147483649 31; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483649 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 2) (fixture s 2 2147483649 31) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483649 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_2_1_7
example (s : riscv_state) : «dfn'SLLW» (7,1,2) (fixture s 2 2147483649 31) =
 (let t := fixture s 2 2147483649 31; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483649 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 7) (fixture s 2 2147483649 31) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483649 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_2_2_0
example (s : riscv_state) : «dfn'SLLW» (0,1,2) (fixture s 2 4294967297 32) =
 (let t := fixture s 2 4294967297 32; t) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967297 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat), 0) (fixture s 2 4294967297 32) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967297 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_2_2_1
example (s : riscv_state) : «dfn'SLLW» (1,1,2) (fixture s 2 4294967297 32) =
 (let t := fixture s 2 4294967297 32; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967297 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat), 1) (fixture s 2 4294967297 32) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967297 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_2_2_2
example (s : riscv_state) : «dfn'SLLW» (2,1,2) (fixture s 2 4294967297 32) =
 (let t := fixture s 2 4294967297 32; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967297 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat), 2) (fixture s 2 4294967297 32) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967297 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_2_2_7
example (s : riscv_state) : «dfn'SLLW» (7,1,2) (fixture s 2 4294967297 32) =
 (let t := fixture s 2 4294967297 32; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967297 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat), 7) (fixture s 2 4294967297 32) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967297 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_2_3_0
example (s : riscv_state) : «dfn'SLLW» (0,1,2) (fixture s 2 18446744073709551615 63) =
 (let t := fixture s 2 18446744073709551615 63; t) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat), 0) (fixture s 2 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_2_3_1
example (s : riscv_state) : «dfn'SLLW» (1,1,2) (fixture s 2 18446744073709551615 63) =
 (let t := fixture s 2 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat), 1) (fixture s 2 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_2_3_2
example (s : riscv_state) : «dfn'SLLW» (2,1,2) (fixture s 2 18446744073709551615 63) =
 (let t := fixture s 2 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat), 2) (fixture s 2 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_2_3_7
example (s : riscv_state) : «dfn'SLLW» (7,1,2) (fixture s 2 18446744073709551615 63) =
 (let t := fixture s 2 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat), 7) (fixture s 2 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_2_4_0
example (s : riscv_state) : «dfn'SLLW» (0,1,2) (fixture s 2 2147483648 64) =
 (let t := fixture s 2 2147483648 64; t) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483648 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat), 0) (fixture s 2 2147483648 64) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483648 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_2_4_1
example (s : riscv_state) : «dfn'SLLW» (1,1,2) (fixture s 2 2147483648 64) =
 (let t := fixture s 2 2147483648 64; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483648 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat), 1) (fixture s 2 2147483648 64) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483648 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_2_4_2
example (s : riscv_state) : «dfn'SLLW» (2,1,2) (fixture s 2 2147483648 64) =
 (let t := fixture s 2 2147483648 64; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483648 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat), 2) (fixture s 2 2147483648 64) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483648 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_2_4_7
example (s : riscv_state) : «dfn'SLLW» (7,1,2) (fixture s 2 2147483648 64) =
 (let t := fixture s 2 2147483648 64; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483648 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat), 7) (fixture s 2 2147483648 64) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483648 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_2_5_0
example (s : riscv_state) : «dfn'SLLW» (0,1,2) (fixture s 2 4294967296 65) =
 (let t := fixture s 2 4294967296 65; t) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967296 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat), 0) (fixture s 2 4294967296 65) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967296 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_2_5_1
example (s : riscv_state) : «dfn'SLLW» (1,1,2) (fixture s 2 4294967296 65) =
 (let t := fixture s 2 4294967296 65; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967296 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat), 1) (fixture s 2 4294967296 65) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967296 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_2_5_2
example (s : riscv_state) : «dfn'SLLW» (2,1,2) (fixture s 2 4294967296 65) =
 (let t := fixture s 2 4294967296 65; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967296 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat), 2) (fixture s 2 4294967296 65) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967296 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_2_5_7
example (s : riscv_state) : «dfn'SLLW» (7,1,2) (fixture s 2 4294967296 65) =
 (let t := fixture s 2 4294967296 65; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967296 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat), 7) (fixture s 2 4294967296 65) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967296 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_2_6_0
example (s : riscv_state) : «dfn'SLLW» (0,1,2) (fixture s 2 9223372036854775809 127) =
 (let t := fixture s 2 9223372036854775809 127; t) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat), 0) (fixture s 2 9223372036854775809 127) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_2_6_1
example (s : riscv_state) : «dfn'SLLW» (1,1,2) (fixture s 2 9223372036854775809 127) =
 (let t := fixture s 2 9223372036854775809 127; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat), 1) (fixture s 2 9223372036854775809 127) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_2_6_2
example (s : riscv_state) : «dfn'SLLW» (2,1,2) (fixture s 2 9223372036854775809 127) =
 (let t := fixture s 2 9223372036854775809 127; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat), 2) (fixture s 2 9223372036854775809 127) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_2_6_7
example (s : riscv_state) : «dfn'SLLW» (7,1,2) (fixture s 2 9223372036854775809 127) =
 (let t := fixture s 2 9223372036854775809 127; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat), 7) (fixture s 2 9223372036854775809 127) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_2_7_0
example (s : riscv_state) : «dfn'SLLW» (0,1,2) (fixture s 2 17 129) =
 (let t := fixture s 2 17 129; t) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (17 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat), 0) (fixture s 2 17 129) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (17 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat)) = (34 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_2_7_1
example (s : riscv_state) : «dfn'SLLW» (1,1,2) (fixture s 2 17 129) =
 (let t := fixture s 2 17 129; {t with c_gpr := holUpdate 7 (holUpdate 1 34 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (17 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat), 1) (fixture s 2 17 129) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (17 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat)) = (34 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_2_7_2
example (s : riscv_state) : «dfn'SLLW» (2,1,2) (fixture s 2 17 129) =
 (let t := fixture s 2 17 129; {t with c_gpr := holUpdate 7 (holUpdate 2 34 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (17 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat), 2) (fixture s 2 17 129) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (17 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat)) = (34 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_2_7_7
example (s : riscv_state) : «dfn'SLLW» (7,1,2) (fixture s 2 17 129) =
 (let t := fixture s 2 17 129; {t with c_gpr := holUpdate 7 (holUpdate 7 34 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (17 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat), 7) (fixture s 2 17 129) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (17 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat)) = (34 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_2_8_0
example (s : riscv_state) : «dfn'SLLW» (0,0,2) (fixture s 2 17 31) =
 (let t := fixture s 2 17 31; t) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (0 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 0) (fixture s 2 17 31) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (0 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_2_8_1
example (s : riscv_state) : «dfn'SLLW» (1,0,2) (fixture s 2 17 31) =
 (let t := fixture s 2 17 31; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (0 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 1) (fixture s 2 17 31) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (0 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_2_8_2
example (s : riscv_state) : «dfn'SLLW» (2,0,2) (fixture s 2 17 31) =
 (let t := fixture s 2 17 31; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (0 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 2) (fixture s 2 17 31) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (0 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_2_8_7
example (s : riscv_state) : «dfn'SLLW» (7,0,2) (fixture s 2 17 31) =
 (let t := fixture s 2 17 31; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (0 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 7) (fixture s 2 17 31) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (0 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_2_9_0
example (s : riscv_state) : «dfn'SLLW» (0,1,0) (fixture s 2 18446744073709551615 63) =
 (let t := fixture s 2 18446744073709551615 63; t) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 0) (fixture s 2 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_2_9_1
example (s : riscv_state) : «dfn'SLLW» (1,1,0) (fixture s 2 18446744073709551615 63) =
 (let t := fixture s 2 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 1) (fixture s 2 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_2_9_2
example (s : riscv_state) : «dfn'SLLW» (2,1,0) (fixture s 2 18446744073709551615 63) =
 (let t := fixture s 2 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 2) (fixture s 2 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_2_9_7
example (s : riscv_state) : «dfn'SLLW» (7,1,0) (fixture s 2 18446744073709551615 63) =
 (let t := fixture s 2 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 7) (fixture s 2 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_3_0_0
example (s : riscv_state) : «dfn'SLLW» (0,1,2) (fixture s 3 9223372036854775808 0) =
 (let t := fixture s 3 9223372036854775808 0; t) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 0) (fixture s 3 9223372036854775808 0) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_3_0_1
example (s : riscv_state) : «dfn'SLLW» (1,1,2) (fixture s 3 9223372036854775808 0) =
 (let t := fixture s 3 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 1) (fixture s 3 9223372036854775808 0) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_3_0_2
example (s : riscv_state) : «dfn'SLLW» (2,1,2) (fixture s 3 9223372036854775808 0) =
 (let t := fixture s 3 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 2) (fixture s 3 9223372036854775808 0) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_3_0_7
example (s : riscv_state) : «dfn'SLLW» (7,1,2) (fixture s 3 9223372036854775808 0) =
 (let t := fixture s 3 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 7) (fixture s 3 9223372036854775808 0) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_3_1_0
example (s : riscv_state) : «dfn'SLLW» (0,1,2) (fixture s 3 2147483649 31) =
 (let t := fixture s 3 2147483649 31; t) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483649 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 0) (fixture s 3 2147483649 31) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483649 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_3_1_1
example (s : riscv_state) : «dfn'SLLW» (1,1,2) (fixture s 3 2147483649 31) =
 (let t := fixture s 3 2147483649 31; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483649 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 1) (fixture s 3 2147483649 31) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483649 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_3_1_2
example (s : riscv_state) : «dfn'SLLW» (2,1,2) (fixture s 3 2147483649 31) =
 (let t := fixture s 3 2147483649 31; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483649 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 2) (fixture s 3 2147483649 31) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483649 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_3_1_7
example (s : riscv_state) : «dfn'SLLW» (7,1,2) (fixture s 3 2147483649 31) =
 (let t := fixture s 3 2147483649 31; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483649 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 7) (fixture s 3 2147483649 31) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483649 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_3_2_0
example (s : riscv_state) : «dfn'SLLW» (0,1,2) (fixture s 3 4294967297 32) =
 (let t := fixture s 3 4294967297 32; t) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967297 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat), 0) (fixture s 3 4294967297 32) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967297 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_3_2_1
example (s : riscv_state) : «dfn'SLLW» (1,1,2) (fixture s 3 4294967297 32) =
 (let t := fixture s 3 4294967297 32; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967297 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat), 1) (fixture s 3 4294967297 32) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967297 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_3_2_2
example (s : riscv_state) : «dfn'SLLW» (2,1,2) (fixture s 3 4294967297 32) =
 (let t := fixture s 3 4294967297 32; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967297 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat), 2) (fixture s 3 4294967297 32) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967297 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_3_2_7
example (s : riscv_state) : «dfn'SLLW» (7,1,2) (fixture s 3 4294967297 32) =
 (let t := fixture s 3 4294967297 32; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967297 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat), 7) (fixture s 3 4294967297 32) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967297 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_3_3_0
example (s : riscv_state) : «dfn'SLLW» (0,1,2) (fixture s 3 18446744073709551615 63) =
 (let t := fixture s 3 18446744073709551615 63; t) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat), 0) (fixture s 3 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_3_3_1
example (s : riscv_state) : «dfn'SLLW» (1,1,2) (fixture s 3 18446744073709551615 63) =
 (let t := fixture s 3 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat), 1) (fixture s 3 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_3_3_2
example (s : riscv_state) : «dfn'SLLW» (2,1,2) (fixture s 3 18446744073709551615 63) =
 (let t := fixture s 3 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat), 2) (fixture s 3 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_3_3_7
example (s : riscv_state) : «dfn'SLLW» (7,1,2) (fixture s 3 18446744073709551615 63) =
 (let t := fixture s 3 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat), 7) (fixture s 3 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_3_4_0
example (s : riscv_state) : «dfn'SLLW» (0,1,2) (fixture s 3 2147483648 64) =
 (let t := fixture s 3 2147483648 64; t) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483648 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat), 0) (fixture s 3 2147483648 64) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483648 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_3_4_1
example (s : riscv_state) : «dfn'SLLW» (1,1,2) (fixture s 3 2147483648 64) =
 (let t := fixture s 3 2147483648 64; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483648 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat), 1) (fixture s 3 2147483648 64) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483648 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_3_4_2
example (s : riscv_state) : «dfn'SLLW» (2,1,2) (fixture s 3 2147483648 64) =
 (let t := fixture s 3 2147483648 64; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483648 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat), 2) (fixture s 3 2147483648 64) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483648 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_3_4_7
example (s : riscv_state) : «dfn'SLLW» (7,1,2) (fixture s 3 2147483648 64) =
 (let t := fixture s 3 2147483648 64; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483648 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat), 7) (fixture s 3 2147483648 64) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483648 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_3_5_0
example (s : riscv_state) : «dfn'SLLW» (0,1,2) (fixture s 3 4294967296 65) =
 (let t := fixture s 3 4294967296 65; t) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967296 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat), 0) (fixture s 3 4294967296 65) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967296 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_3_5_1
example (s : riscv_state) : «dfn'SLLW» (1,1,2) (fixture s 3 4294967296 65) =
 (let t := fixture s 3 4294967296 65; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967296 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat), 1) (fixture s 3 4294967296 65) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967296 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_3_5_2
example (s : riscv_state) : «dfn'SLLW» (2,1,2) (fixture s 3 4294967296 65) =
 (let t := fixture s 3 4294967296 65; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967296 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat), 2) (fixture s 3 4294967296 65) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967296 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_3_5_7
example (s : riscv_state) : «dfn'SLLW» (7,1,2) (fixture s 3 4294967296 65) =
 (let t := fixture s 3 4294967296 65; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967296 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat), 7) (fixture s 3 4294967296 65) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967296 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_3_6_0
example (s : riscv_state) : «dfn'SLLW» (0,1,2) (fixture s 3 9223372036854775809 127) =
 (let t := fixture s 3 9223372036854775809 127; t) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat), 0) (fixture s 3 9223372036854775809 127) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_3_6_1
example (s : riscv_state) : «dfn'SLLW» (1,1,2) (fixture s 3 9223372036854775809 127) =
 (let t := fixture s 3 9223372036854775809 127; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat), 1) (fixture s 3 9223372036854775809 127) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_3_6_2
example (s : riscv_state) : «dfn'SLLW» (2,1,2) (fixture s 3 9223372036854775809 127) =
 (let t := fixture s 3 9223372036854775809 127; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat), 2) (fixture s 3 9223372036854775809 127) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_3_6_7
example (s : riscv_state) : «dfn'SLLW» (7,1,2) (fixture s 3 9223372036854775809 127) =
 (let t := fixture s 3 9223372036854775809 127; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat), 7) (fixture s 3 9223372036854775809 127) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_3_7_0
example (s : riscv_state) : «dfn'SLLW» (0,1,2) (fixture s 3 17 129) =
 (let t := fixture s 3 17 129; t) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (17 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat), 0) (fixture s 3 17 129) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (17 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat)) = (34 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_3_7_1
example (s : riscv_state) : «dfn'SLLW» (1,1,2) (fixture s 3 17 129) =
 (let t := fixture s 3 17 129; {t with c_gpr := holUpdate 7 (holUpdate 1 34 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (17 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat), 1) (fixture s 3 17 129) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (17 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat)) = (34 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_3_7_2
example (s : riscv_state) : «dfn'SLLW» (2,1,2) (fixture s 3 17 129) =
 (let t := fixture s 3 17 129; {t with c_gpr := holUpdate 7 (holUpdate 2 34 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (17 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat), 2) (fixture s 3 17 129) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (17 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat)) = (34 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_3_7_7
example (s : riscv_state) : «dfn'SLLW» (7,1,2) (fixture s 3 17 129) =
 (let t := fixture s 3 17 129; {t with c_gpr := holUpdate 7 (holUpdate 7 34 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (17 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat), 7) (fixture s 3 17 129) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (17 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat)) = (34 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_3_8_0
example (s : riscv_state) : «dfn'SLLW» (0,0,2) (fixture s 3 17 31) =
 (let t := fixture s 3 17 31; t) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (0 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 0) (fixture s 3 17 31) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (0 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_3_8_1
example (s : riscv_state) : «dfn'SLLW» (1,0,2) (fixture s 3 17 31) =
 (let t := fixture s 3 17 31; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (0 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 1) (fixture s 3 17 31) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (0 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_3_8_2
example (s : riscv_state) : «dfn'SLLW» (2,0,2) (fixture s 3 17 31) =
 (let t := fixture s 3 17 31; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (0 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 2) (fixture s 3 17 31) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (0 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_3_8_7
example (s : riscv_state) : «dfn'SLLW» (7,0,2) (fixture s 3 17 31) =
 (let t := fixture s 3 17 31; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (0 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 7) (fixture s 3 17 31) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (0 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_3_9_0
example (s : riscv_state) : «dfn'SLLW» (0,1,0) (fixture s 3 18446744073709551615 63) =
 (let t := fixture s 3 18446744073709551615 63; t) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 0) (fixture s 3 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_3_9_1
example (s : riscv_state) : «dfn'SLLW» (1,1,0) (fixture s 3 18446744073709551615 63) =
 (let t := fixture s 3 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 1) (fixture s 3 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_3_9_2
example (s : riscv_state) : «dfn'SLLW» (2,1,0) (fixture s 3 18446744073709551615 63) =
 (let t := fixture s 3 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 2) (fixture s 3 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SLLW_3_9_7
example (s : riscv_state) : «dfn'SLLW» (7,1,0) (fixture s 3 18446744073709551615 63) =
 (let t := fixture s 3 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 7) (fixture s 3 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) <<< (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_0_0_0
example (s : riscv_state) : «dfn'SRL» (0,1,2) (fixture s 0 9223372036854775808 0) =
 (let t := fixture s 0 9223372036854775808 0; t) := by
  change «write'GPR» (BitVec.setWidth 64 ((holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 0) (fixture s 0 9223372036854775808 0) = _
  have numeric : (BitVec.setWidth 64 ((holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_0_0_1
example (s : riscv_state) : «dfn'SRL» (1,1,2) (fixture s 0 9223372036854775808 0) =
 (let t := fixture s 0 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.setWidth 64 ((holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 1) (fixture s 0 9223372036854775808 0) = _
  have numeric : (BitVec.setWidth 64 ((holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_0_0_2
example (s : riscv_state) : «dfn'SRL» (2,1,2) (fixture s 0 9223372036854775808 0) =
 (let t := fixture s 0 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.setWidth 64 ((holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 2) (fixture s 0 9223372036854775808 0) = _
  have numeric : (BitVec.setWidth 64 ((holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_0_0_7
example (s : riscv_state) : «dfn'SRL» (7,1,2) (fixture s 0 9223372036854775808 0) =
 (let t := fixture s 0 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.setWidth 64 ((holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 7) (fixture s 0 9223372036854775808 0) = _
  have numeric : (BitVec.setWidth 64 ((holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_0_1_0
example (s : riscv_state) : «dfn'SRL» (0,1,2) (fixture s 0 2147483649 31) =
 (let t := fixture s 0 2147483649 31; t) := by
  change «write'GPR» (BitVec.setWidth 64 ((holWordExtract 32 31 0 (2147483649 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 0) (fixture s 0 2147483649 31) = _
  have numeric : (BitVec.setWidth 64 ((holWordExtract 32 31 0 (2147483649 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_0_1_1
example (s : riscv_state) : «dfn'SRL» (1,1,2) (fixture s 0 2147483649 31) =
 (let t := fixture s 0 2147483649 31; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.setWidth 64 ((holWordExtract 32 31 0 (2147483649 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 1) (fixture s 0 2147483649 31) = _
  have numeric : (BitVec.setWidth 64 ((holWordExtract 32 31 0 (2147483649 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_0_1_2
example (s : riscv_state) : «dfn'SRL» (2,1,2) (fixture s 0 2147483649 31) =
 (let t := fixture s 0 2147483649 31; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.setWidth 64 ((holWordExtract 32 31 0 (2147483649 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 2) (fixture s 0 2147483649 31) = _
  have numeric : (BitVec.setWidth 64 ((holWordExtract 32 31 0 (2147483649 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_0_1_7
example (s : riscv_state) : «dfn'SRL» (7,1,2) (fixture s 0 2147483649 31) =
 (let t := fixture s 0 2147483649 31; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.setWidth 64 ((holWordExtract 32 31 0 (2147483649 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 7) (fixture s 0 2147483649 31) = _
  have numeric : (BitVec.setWidth 64 ((holWordExtract 32 31 0 (2147483649 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_0_2_0
example (s : riscv_state) : «dfn'SRL» (0,1,2) (fixture s 0 4294967297 32) =
 (let t := fixture s 0 4294967297 32; t) := by
  change «write'GPR» (BitVec.setWidth 64 ((holWordExtract 32 31 0 (4294967297 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat), 0) (fixture s 0 4294967297 32) = _
  have numeric : (BitVec.setWidth 64 ((holWordExtract 32 31 0 (4294967297 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_0_2_1
example (s : riscv_state) : «dfn'SRL» (1,1,2) (fixture s 0 4294967297 32) =
 (let t := fixture s 0 4294967297 32; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.setWidth 64 ((holWordExtract 32 31 0 (4294967297 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat), 1) (fixture s 0 4294967297 32) = _
  have numeric : (BitVec.setWidth 64 ((holWordExtract 32 31 0 (4294967297 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_0_2_2
example (s : riscv_state) : «dfn'SRL» (2,1,2) (fixture s 0 4294967297 32) =
 (let t := fixture s 0 4294967297 32; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.setWidth 64 ((holWordExtract 32 31 0 (4294967297 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat), 2) (fixture s 0 4294967297 32) = _
  have numeric : (BitVec.setWidth 64 ((holWordExtract 32 31 0 (4294967297 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_0_2_7
example (s : riscv_state) : «dfn'SRL» (7,1,2) (fixture s 0 4294967297 32) =
 (let t := fixture s 0 4294967297 32; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.setWidth 64 ((holWordExtract 32 31 0 (4294967297 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat), 7) (fixture s 0 4294967297 32) = _
  have numeric : (BitVec.setWidth 64 ((holWordExtract 32 31 0 (4294967297 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_0_3_0
example (s : riscv_state) : «dfn'SRL» (0,1,2) (fixture s 0 18446744073709551615 63) =
 (let t := fixture s 0 18446744073709551615 63; t) := by
  change «write'GPR» (BitVec.setWidth 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat), 0) (fixture s 0 18446744073709551615 63) = _
  have numeric : (BitVec.setWidth 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_0_3_1
example (s : riscv_state) : «dfn'SRL» (1,1,2) (fixture s 0 18446744073709551615 63) =
 (let t := fixture s 0 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.setWidth 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat), 1) (fixture s 0 18446744073709551615 63) = _
  have numeric : (BitVec.setWidth 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_0_3_2
example (s : riscv_state) : «dfn'SRL» (2,1,2) (fixture s 0 18446744073709551615 63) =
 (let t := fixture s 0 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.setWidth 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat), 2) (fixture s 0 18446744073709551615 63) = _
  have numeric : (BitVec.setWidth 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_0_3_7
example (s : riscv_state) : «dfn'SRL» (7,1,2) (fixture s 0 18446744073709551615 63) =
 (let t := fixture s 0 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.setWidth 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat), 7) (fixture s 0 18446744073709551615 63) = _
  have numeric : (BitVec.setWidth 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_0_4_0
example (s : riscv_state) : «dfn'SRL» (0,1,2) (fixture s 0 2147483648 64) =
 (let t := fixture s 0 2147483648 64; t) := by
  change «write'GPR» (BitVec.setWidth 64 ((holWordExtract 32 31 0 (2147483648 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat), 0) (fixture s 0 2147483648 64) = _
  have numeric : (BitVec.setWidth 64 ((holWordExtract 32 31 0 (2147483648 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_0_4_1
example (s : riscv_state) : «dfn'SRL» (1,1,2) (fixture s 0 2147483648 64) =
 (let t := fixture s 0 2147483648 64; {t with c_gpr := holUpdate 7 (holUpdate 1 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.setWidth 64 ((holWordExtract 32 31 0 (2147483648 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat), 1) (fixture s 0 2147483648 64) = _
  have numeric : (BitVec.setWidth 64 ((holWordExtract 32 31 0 (2147483648 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_0_4_2
example (s : riscv_state) : «dfn'SRL» (2,1,2) (fixture s 0 2147483648 64) =
 (let t := fixture s 0 2147483648 64; {t with c_gpr := holUpdate 7 (holUpdate 2 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.setWidth 64 ((holWordExtract 32 31 0 (2147483648 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat), 2) (fixture s 0 2147483648 64) = _
  have numeric : (BitVec.setWidth 64 ((holWordExtract 32 31 0 (2147483648 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_0_4_7
example (s : riscv_state) : «dfn'SRL» (7,1,2) (fixture s 0 2147483648 64) =
 (let t := fixture s 0 2147483648 64; {t with c_gpr := holUpdate 7 (holUpdate 7 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.setWidth 64 ((holWordExtract 32 31 0 (2147483648 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat), 7) (fixture s 0 2147483648 64) = _
  have numeric : (BitVec.setWidth 64 ((holWordExtract 32 31 0 (2147483648 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_0_5_0
example (s : riscv_state) : «dfn'SRL» (0,1,2) (fixture s 0 4294967296 65) =
 (let t := fixture s 0 4294967296 65; t) := by
  change «write'GPR» (BitVec.setWidth 64 ((holWordExtract 32 31 0 (4294967296 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat), 0) (fixture s 0 4294967296 65) = _
  have numeric : (BitVec.setWidth 64 ((holWordExtract 32 31 0 (4294967296 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_0_5_1
example (s : riscv_state) : «dfn'SRL» (1,1,2) (fixture s 0 4294967296 65) =
 (let t := fixture s 0 4294967296 65; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.setWidth 64 ((holWordExtract 32 31 0 (4294967296 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat), 1) (fixture s 0 4294967296 65) = _
  have numeric : (BitVec.setWidth 64 ((holWordExtract 32 31 0 (4294967296 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_0_5_2
example (s : riscv_state) : «dfn'SRL» (2,1,2) (fixture s 0 4294967296 65) =
 (let t := fixture s 0 4294967296 65; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.setWidth 64 ((holWordExtract 32 31 0 (4294967296 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat), 2) (fixture s 0 4294967296 65) = _
  have numeric : (BitVec.setWidth 64 ((holWordExtract 32 31 0 (4294967296 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_0_5_7
example (s : riscv_state) : «dfn'SRL» (7,1,2) (fixture s 0 4294967296 65) =
 (let t := fixture s 0 4294967296 65; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.setWidth 64 ((holWordExtract 32 31 0 (4294967296 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat), 7) (fixture s 0 4294967296 65) = _
  have numeric : (BitVec.setWidth 64 ((holWordExtract 32 31 0 (4294967296 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_0_6_0
example (s : riscv_state) : «dfn'SRL» (0,1,2) (fixture s 0 9223372036854775809 127) =
 (let t := fixture s 0 9223372036854775809 127; t) := by
  change «write'GPR» (BitVec.setWidth 64 ((holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat), 0) (fixture s 0 9223372036854775809 127) = _
  have numeric : (BitVec.setWidth 64 ((holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_0_6_1
example (s : riscv_state) : «dfn'SRL» (1,1,2) (fixture s 0 9223372036854775809 127) =
 (let t := fixture s 0 9223372036854775809 127; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.setWidth 64 ((holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat), 1) (fixture s 0 9223372036854775809 127) = _
  have numeric : (BitVec.setWidth 64 ((holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_0_6_2
example (s : riscv_state) : «dfn'SRL» (2,1,2) (fixture s 0 9223372036854775809 127) =
 (let t := fixture s 0 9223372036854775809 127; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.setWidth 64 ((holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat), 2) (fixture s 0 9223372036854775809 127) = _
  have numeric : (BitVec.setWidth 64 ((holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_0_6_7
example (s : riscv_state) : «dfn'SRL» (7,1,2) (fixture s 0 9223372036854775809 127) =
 (let t := fixture s 0 9223372036854775809 127; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.setWidth 64 ((holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat), 7) (fixture s 0 9223372036854775809 127) = _
  have numeric : (BitVec.setWidth 64 ((holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_0_7_0
example (s : riscv_state) : «dfn'SRL» (0,1,2) (fixture s 0 17 129) =
 (let t := fixture s 0 17 129; t) := by
  change «write'GPR» (BitVec.setWidth 64 ((holWordExtract 32 31 0 (17 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat), 0) (fixture s 0 17 129) = _
  have numeric : (BitVec.setWidth 64 ((holWordExtract 32 31 0 (17 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat)) = (8 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_0_7_1
example (s : riscv_state) : «dfn'SRL» (1,1,2) (fixture s 0 17 129) =
 (let t := fixture s 0 17 129; {t with c_gpr := holUpdate 7 (holUpdate 1 8 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.setWidth 64 ((holWordExtract 32 31 0 (17 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat), 1) (fixture s 0 17 129) = _
  have numeric : (BitVec.setWidth 64 ((holWordExtract 32 31 0 (17 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat)) = (8 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_0_7_2
example (s : riscv_state) : «dfn'SRL» (2,1,2) (fixture s 0 17 129) =
 (let t := fixture s 0 17 129; {t with c_gpr := holUpdate 7 (holUpdate 2 8 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.setWidth 64 ((holWordExtract 32 31 0 (17 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat), 2) (fixture s 0 17 129) = _
  have numeric : (BitVec.setWidth 64 ((holWordExtract 32 31 0 (17 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat)) = (8 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_0_7_7
example (s : riscv_state) : «dfn'SRL» (7,1,2) (fixture s 0 17 129) =
 (let t := fixture s 0 17 129; {t with c_gpr := holUpdate 7 (holUpdate 7 8 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.setWidth 64 ((holWordExtract 32 31 0 (17 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat), 7) (fixture s 0 17 129) = _
  have numeric : (BitVec.setWidth 64 ((holWordExtract 32 31 0 (17 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat)) = (8 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_0_8_0
example (s : riscv_state) : «dfn'SRL» (0,0,2) (fixture s 0 17 31) =
 (let t := fixture s 0 17 31; t) := by
  change «write'GPR» (BitVec.setWidth 64 ((holWordExtract 32 31 0 (0 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 0) (fixture s 0 17 31) = _
  have numeric : (BitVec.setWidth 64 ((holWordExtract 32 31 0 (0 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_0_8_1
example (s : riscv_state) : «dfn'SRL» (1,0,2) (fixture s 0 17 31) =
 (let t := fixture s 0 17 31; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.setWidth 64 ((holWordExtract 32 31 0 (0 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 1) (fixture s 0 17 31) = _
  have numeric : (BitVec.setWidth 64 ((holWordExtract 32 31 0 (0 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_0_8_2
example (s : riscv_state) : «dfn'SRL» (2,0,2) (fixture s 0 17 31) =
 (let t := fixture s 0 17 31; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.setWidth 64 ((holWordExtract 32 31 0 (0 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 2) (fixture s 0 17 31) = _
  have numeric : (BitVec.setWidth 64 ((holWordExtract 32 31 0 (0 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_0_8_7
example (s : riscv_state) : «dfn'SRL» (7,0,2) (fixture s 0 17 31) =
 (let t := fixture s 0 17 31; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.setWidth 64 ((holWordExtract 32 31 0 (0 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 7) (fixture s 0 17 31) = _
  have numeric : (BitVec.setWidth 64 ((holWordExtract 32 31 0 (0 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_0_9_0
example (s : riscv_state) : «dfn'SRL» (0,1,0) (fixture s 0 18446744073709551615 63) =
 (let t := fixture s 0 18446744073709551615 63; t) := by
  change «write'GPR» (BitVec.setWidth 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 0) (fixture s 0 18446744073709551615 63) = _
  have numeric : (BitVec.setWidth 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (4294967295 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_0_9_1
example (s : riscv_state) : «dfn'SRL» (1,1,0) (fixture s 0 18446744073709551615 63) =
 (let t := fixture s 0 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 1 4294967295 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.setWidth 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 1) (fixture s 0 18446744073709551615 63) = _
  have numeric : (BitVec.setWidth 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (4294967295 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_0_9_2
example (s : riscv_state) : «dfn'SRL» (2,1,0) (fixture s 0 18446744073709551615 63) =
 (let t := fixture s 0 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 2 4294967295 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.setWidth 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 2) (fixture s 0 18446744073709551615 63) = _
  have numeric : (BitVec.setWidth 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (4294967295 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_0_9_7
example (s : riscv_state) : «dfn'SRL» (7,1,0) (fixture s 0 18446744073709551615 63) =
 (let t := fixture s 0 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 7 4294967295 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.setWidth 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 7) (fixture s 0 18446744073709551615 63) = _
  have numeric : (BitVec.setWidth 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (4294967295 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_2_0_0
example (s : riscv_state) : «dfn'SRL» (0,1,2) (fixture s 2 9223372036854775808 0) =
 (let t := fixture s 2 9223372036854775808 0; t) := by
  change «write'GPR» (((9223372036854775808 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat), 0) (fixture s 2 9223372036854775808 0) = _
  have numeric : (((9223372036854775808 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_2_0_1
example (s : riscv_state) : «dfn'SRL» (1,1,2) (fixture s 2 9223372036854775808 0) =
 (let t := fixture s 2 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 1 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775808 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat), 1) (fixture s 2 9223372036854775808 0) = _
  have numeric : (((9223372036854775808 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_2_0_2
example (s : riscv_state) : «dfn'SRL» (2,1,2) (fixture s 2 9223372036854775808 0) =
 (let t := fixture s 2 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 2 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775808 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat), 2) (fixture s 2 9223372036854775808 0) = _
  have numeric : (((9223372036854775808 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_2_0_7
example (s : riscv_state) : «dfn'SRL» (7,1,2) (fixture s 2 9223372036854775808 0) =
 (let t := fixture s 2 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 7 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775808 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat), 7) (fixture s 2 9223372036854775808 0) = _
  have numeric : (((9223372036854775808 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_2_1_0
example (s : riscv_state) : «dfn'SRL» (0,1,2) (fixture s 2 2147483649 31) =
 (let t := fixture s 2 2147483649 31; t) := by
  change «write'GPR» (((2147483649 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat), 0) (fixture s 2 2147483649 31) = _
  have numeric : (((2147483649 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_2_1_1
example (s : riscv_state) : «dfn'SRL» (1,1,2) (fixture s 2 2147483649 31) =
 (let t := fixture s 2 2147483649 31; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((2147483649 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat), 1) (fixture s 2 2147483649 31) = _
  have numeric : (((2147483649 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_2_1_2
example (s : riscv_state) : «dfn'SRL» (2,1,2) (fixture s 2 2147483649 31) =
 (let t := fixture s 2 2147483649 31; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((2147483649 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat), 2) (fixture s 2 2147483649 31) = _
  have numeric : (((2147483649 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_2_1_7
example (s : riscv_state) : «dfn'SRL» (7,1,2) (fixture s 2 2147483649 31) =
 (let t := fixture s 2 2147483649 31; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((2147483649 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat), 7) (fixture s 2 2147483649 31) = _
  have numeric : (((2147483649 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_2_2_0
example (s : riscv_state) : «dfn'SRL» (0,1,2) (fixture s 2 4294967297 32) =
 (let t := fixture s 2 4294967297 32; t) := by
  change «write'GPR» (((4294967297 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (32 : BitVec 64))).toNat), 0) (fixture s 2 4294967297 32) = _
  have numeric : (((4294967297 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (32 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_2_2_1
example (s : riscv_state) : «dfn'SRL» (1,1,2) (fixture s 2 4294967297 32) =
 (let t := fixture s 2 4294967297 32; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((4294967297 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (32 : BitVec 64))).toNat), 1) (fixture s 2 4294967297 32) = _
  have numeric : (((4294967297 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (32 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_2_2_2
example (s : riscv_state) : «dfn'SRL» (2,1,2) (fixture s 2 4294967297 32) =
 (let t := fixture s 2 4294967297 32; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((4294967297 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (32 : BitVec 64))).toNat), 2) (fixture s 2 4294967297 32) = _
  have numeric : (((4294967297 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (32 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_2_2_7
example (s : riscv_state) : «dfn'SRL» (7,1,2) (fixture s 2 4294967297 32) =
 (let t := fixture s 2 4294967297 32; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((4294967297 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (32 : BitVec 64))).toNat), 7) (fixture s 2 4294967297 32) = _
  have numeric : (((4294967297 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (32 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_2_3_0
example (s : riscv_state) : «dfn'SRL» (0,1,2) (fixture s 2 18446744073709551615 63) =
 (let t := fixture s 2 18446744073709551615 63; t) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (63 : BitVec 64))).toNat), 0) (fixture s 2 18446744073709551615 63) = _
  have numeric : (((18446744073709551615 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (63 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_2_3_1
example (s : riscv_state) : «dfn'SRL» (1,1,2) (fixture s 2 18446744073709551615 63) =
 (let t := fixture s 2 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (63 : BitVec 64))).toNat), 1) (fixture s 2 18446744073709551615 63) = _
  have numeric : (((18446744073709551615 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (63 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_2_3_2
example (s : riscv_state) : «dfn'SRL» (2,1,2) (fixture s 2 18446744073709551615 63) =
 (let t := fixture s 2 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (63 : BitVec 64))).toNat), 2) (fixture s 2 18446744073709551615 63) = _
  have numeric : (((18446744073709551615 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (63 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_2_3_7
example (s : riscv_state) : «dfn'SRL» (7,1,2) (fixture s 2 18446744073709551615 63) =
 (let t := fixture s 2 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (63 : BitVec 64))).toNat), 7) (fixture s 2 18446744073709551615 63) = _
  have numeric : (((18446744073709551615 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (63 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_2_4_0
example (s : riscv_state) : «dfn'SRL» (0,1,2) (fixture s 2 2147483648 64) =
 (let t := fixture s 2 2147483648 64; t) := by
  change «write'GPR» (((2147483648 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (64 : BitVec 64))).toNat), 0) (fixture s 2 2147483648 64) = _
  have numeric : (((2147483648 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (64 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_2_4_1
example (s : riscv_state) : «dfn'SRL» (1,1,2) (fixture s 2 2147483648 64) =
 (let t := fixture s 2 2147483648 64; {t with c_gpr := holUpdate 7 (holUpdate 1 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((2147483648 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (64 : BitVec 64))).toNat), 1) (fixture s 2 2147483648 64) = _
  have numeric : (((2147483648 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (64 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_2_4_2
example (s : riscv_state) : «dfn'SRL» (2,1,2) (fixture s 2 2147483648 64) =
 (let t := fixture s 2 2147483648 64; {t with c_gpr := holUpdate 7 (holUpdate 2 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((2147483648 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (64 : BitVec 64))).toNat), 2) (fixture s 2 2147483648 64) = _
  have numeric : (((2147483648 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (64 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_2_4_7
example (s : riscv_state) : «dfn'SRL» (7,1,2) (fixture s 2 2147483648 64) =
 (let t := fixture s 2 2147483648 64; {t with c_gpr := holUpdate 7 (holUpdate 7 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((2147483648 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (64 : BitVec 64))).toNat), 7) (fixture s 2 2147483648 64) = _
  have numeric : (((2147483648 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (64 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_2_5_0
example (s : riscv_state) : «dfn'SRL» (0,1,2) (fixture s 2 4294967296 65) =
 (let t := fixture s 2 4294967296 65; t) := by
  change «write'GPR» (((4294967296 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (65 : BitVec 64))).toNat), 0) (fixture s 2 4294967296 65) = _
  have numeric : (((4294967296 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (65 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_2_5_1
example (s : riscv_state) : «dfn'SRL» (1,1,2) (fixture s 2 4294967296 65) =
 (let t := fixture s 2 4294967296 65; {t with c_gpr := holUpdate 7 (holUpdate 1 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((4294967296 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (65 : BitVec 64))).toNat), 1) (fixture s 2 4294967296 65) = _
  have numeric : (((4294967296 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (65 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_2_5_2
example (s : riscv_state) : «dfn'SRL» (2,1,2) (fixture s 2 4294967296 65) =
 (let t := fixture s 2 4294967296 65; {t with c_gpr := holUpdate 7 (holUpdate 2 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((4294967296 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (65 : BitVec 64))).toNat), 2) (fixture s 2 4294967296 65) = _
  have numeric : (((4294967296 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (65 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_2_5_7
example (s : riscv_state) : «dfn'SRL» (7,1,2) (fixture s 2 4294967296 65) =
 (let t := fixture s 2 4294967296 65; {t with c_gpr := holUpdate 7 (holUpdate 7 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((4294967296 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (65 : BitVec 64))).toNat), 7) (fixture s 2 4294967296 65) = _
  have numeric : (((4294967296 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (65 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_2_6_0
example (s : riscv_state) : «dfn'SRL» (0,1,2) (fixture s 2 9223372036854775809 127) =
 (let t := fixture s 2 9223372036854775809 127; t) := by
  change «write'GPR» (((9223372036854775809 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (127 : BitVec 64))).toNat), 0) (fixture s 2 9223372036854775809 127) = _
  have numeric : (((9223372036854775809 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (127 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_2_6_1
example (s : riscv_state) : «dfn'SRL» (1,1,2) (fixture s 2 9223372036854775809 127) =
 (let t := fixture s 2 9223372036854775809 127; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775809 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (127 : BitVec 64))).toNat), 1) (fixture s 2 9223372036854775809 127) = _
  have numeric : (((9223372036854775809 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (127 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_2_6_2
example (s : riscv_state) : «dfn'SRL» (2,1,2) (fixture s 2 9223372036854775809 127) =
 (let t := fixture s 2 9223372036854775809 127; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775809 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (127 : BitVec 64))).toNat), 2) (fixture s 2 9223372036854775809 127) = _
  have numeric : (((9223372036854775809 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (127 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_2_6_7
example (s : riscv_state) : «dfn'SRL» (7,1,2) (fixture s 2 9223372036854775809 127) =
 (let t := fixture s 2 9223372036854775809 127; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775809 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (127 : BitVec 64))).toNat), 7) (fixture s 2 9223372036854775809 127) = _
  have numeric : (((9223372036854775809 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (127 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_2_7_0
example (s : riscv_state) : «dfn'SRL» (0,1,2) (fixture s 2 17 129) =
 (let t := fixture s 2 17 129; t) := by
  change «write'GPR» (((17 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (129 : BitVec 64))).toNat), 0) (fixture s 2 17 129) = _
  have numeric : (((17 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (129 : BitVec 64))).toNat)) = (8 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_2_7_1
example (s : riscv_state) : «dfn'SRL» (1,1,2) (fixture s 2 17 129) =
 (let t := fixture s 2 17 129; {t with c_gpr := holUpdate 7 (holUpdate 1 8 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((17 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (129 : BitVec 64))).toNat), 1) (fixture s 2 17 129) = _
  have numeric : (((17 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (129 : BitVec 64))).toNat)) = (8 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_2_7_2
example (s : riscv_state) : «dfn'SRL» (2,1,2) (fixture s 2 17 129) =
 (let t := fixture s 2 17 129; {t with c_gpr := holUpdate 7 (holUpdate 2 8 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((17 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (129 : BitVec 64))).toNat), 2) (fixture s 2 17 129) = _
  have numeric : (((17 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (129 : BitVec 64))).toNat)) = (8 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_2_7_7
example (s : riscv_state) : «dfn'SRL» (7,1,2) (fixture s 2 17 129) =
 (let t := fixture s 2 17 129; {t with c_gpr := holUpdate 7 (holUpdate 7 8 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((17 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (129 : BitVec 64))).toNat), 7) (fixture s 2 17 129) = _
  have numeric : (((17 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (129 : BitVec 64))).toNat)) = (8 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_2_8_0
example (s : riscv_state) : «dfn'SRL» (0,0,2) (fixture s 2 17 31) =
 (let t := fixture s 2 17 31; t) := by
  change «write'GPR» (((0 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat), 0) (fixture s 2 17 31) = _
  have numeric : (((0 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_2_8_1
example (s : riscv_state) : «dfn'SRL» (1,0,2) (fixture s 2 17 31) =
 (let t := fixture s 2 17 31; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((0 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat), 1) (fixture s 2 17 31) = _
  have numeric : (((0 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_2_8_2
example (s : riscv_state) : «dfn'SRL» (2,0,2) (fixture s 2 17 31) =
 (let t := fixture s 2 17 31; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((0 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat), 2) (fixture s 2 17 31) = _
  have numeric : (((0 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_2_8_7
example (s : riscv_state) : «dfn'SRL» (7,0,2) (fixture s 2 17 31) =
 (let t := fixture s 2 17 31; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((0 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat), 7) (fixture s 2 17 31) = _
  have numeric : (((0 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_2_9_0
example (s : riscv_state) : «dfn'SRL» (0,1,0) (fixture s 2 18446744073709551615 63) =
 (let t := fixture s 2 18446744073709551615 63; t) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat), 0) (fixture s 2 18446744073709551615 63) = _
  have numeric : (((18446744073709551615 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_2_9_1
example (s : riscv_state) : «dfn'SRL» (1,1,0) (fixture s 2 18446744073709551615 63) =
 (let t := fixture s 2 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat), 1) (fixture s 2 18446744073709551615 63) = _
  have numeric : (((18446744073709551615 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_2_9_2
example (s : riscv_state) : «dfn'SRL» (2,1,0) (fixture s 2 18446744073709551615 63) =
 (let t := fixture s 2 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat), 2) (fixture s 2 18446744073709551615 63) = _
  have numeric : (((18446744073709551615 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_2_9_7
example (s : riscv_state) : «dfn'SRL» (7,1,0) (fixture s 2 18446744073709551615 63) =
 (let t := fixture s 2 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat), 7) (fixture s 2 18446744073709551615 63) = _
  have numeric : (((18446744073709551615 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_3_0_0
example (s : riscv_state) : «dfn'SRL» (0,1,2) (fixture s 3 9223372036854775808 0) =
 (let t := fixture s 3 9223372036854775808 0; t) := by
  change «write'GPR» (((9223372036854775808 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat), 0) (fixture s 3 9223372036854775808 0) = _
  have numeric : (((9223372036854775808 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_3_0_1
example (s : riscv_state) : «dfn'SRL» (1,1,2) (fixture s 3 9223372036854775808 0) =
 (let t := fixture s 3 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 1 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775808 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat), 1) (fixture s 3 9223372036854775808 0) = _
  have numeric : (((9223372036854775808 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_3_0_2
example (s : riscv_state) : «dfn'SRL» (2,1,2) (fixture s 3 9223372036854775808 0) =
 (let t := fixture s 3 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 2 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775808 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat), 2) (fixture s 3 9223372036854775808 0) = _
  have numeric : (((9223372036854775808 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_3_0_7
example (s : riscv_state) : «dfn'SRL» (7,1,2) (fixture s 3 9223372036854775808 0) =
 (let t := fixture s 3 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 7 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775808 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat), 7) (fixture s 3 9223372036854775808 0) = _
  have numeric : (((9223372036854775808 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_3_1_0
example (s : riscv_state) : «dfn'SRL» (0,1,2) (fixture s 3 2147483649 31) =
 (let t := fixture s 3 2147483649 31; t) := by
  change «write'GPR» (((2147483649 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat), 0) (fixture s 3 2147483649 31) = _
  have numeric : (((2147483649 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_3_1_1
example (s : riscv_state) : «dfn'SRL» (1,1,2) (fixture s 3 2147483649 31) =
 (let t := fixture s 3 2147483649 31; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((2147483649 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat), 1) (fixture s 3 2147483649 31) = _
  have numeric : (((2147483649 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_3_1_2
example (s : riscv_state) : «dfn'SRL» (2,1,2) (fixture s 3 2147483649 31) =
 (let t := fixture s 3 2147483649 31; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((2147483649 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat), 2) (fixture s 3 2147483649 31) = _
  have numeric : (((2147483649 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_3_1_7
example (s : riscv_state) : «dfn'SRL» (7,1,2) (fixture s 3 2147483649 31) =
 (let t := fixture s 3 2147483649 31; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((2147483649 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat), 7) (fixture s 3 2147483649 31) = _
  have numeric : (((2147483649 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_3_2_0
example (s : riscv_state) : «dfn'SRL» (0,1,2) (fixture s 3 4294967297 32) =
 (let t := fixture s 3 4294967297 32; t) := by
  change «write'GPR» (((4294967297 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (32 : BitVec 64))).toNat), 0) (fixture s 3 4294967297 32) = _
  have numeric : (((4294967297 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (32 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_3_2_1
example (s : riscv_state) : «dfn'SRL» (1,1,2) (fixture s 3 4294967297 32) =
 (let t := fixture s 3 4294967297 32; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((4294967297 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (32 : BitVec 64))).toNat), 1) (fixture s 3 4294967297 32) = _
  have numeric : (((4294967297 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (32 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_3_2_2
example (s : riscv_state) : «dfn'SRL» (2,1,2) (fixture s 3 4294967297 32) =
 (let t := fixture s 3 4294967297 32; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((4294967297 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (32 : BitVec 64))).toNat), 2) (fixture s 3 4294967297 32) = _
  have numeric : (((4294967297 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (32 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_3_2_7
example (s : riscv_state) : «dfn'SRL» (7,1,2) (fixture s 3 4294967297 32) =
 (let t := fixture s 3 4294967297 32; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((4294967297 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (32 : BitVec 64))).toNat), 7) (fixture s 3 4294967297 32) = _
  have numeric : (((4294967297 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (32 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_3_3_0
example (s : riscv_state) : «dfn'SRL» (0,1,2) (fixture s 3 18446744073709551615 63) =
 (let t := fixture s 3 18446744073709551615 63; t) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (63 : BitVec 64))).toNat), 0) (fixture s 3 18446744073709551615 63) = _
  have numeric : (((18446744073709551615 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (63 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_3_3_1
example (s : riscv_state) : «dfn'SRL» (1,1,2) (fixture s 3 18446744073709551615 63) =
 (let t := fixture s 3 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (63 : BitVec 64))).toNat), 1) (fixture s 3 18446744073709551615 63) = _
  have numeric : (((18446744073709551615 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (63 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_3_3_2
example (s : riscv_state) : «dfn'SRL» (2,1,2) (fixture s 3 18446744073709551615 63) =
 (let t := fixture s 3 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (63 : BitVec 64))).toNat), 2) (fixture s 3 18446744073709551615 63) = _
  have numeric : (((18446744073709551615 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (63 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_3_3_7
example (s : riscv_state) : «dfn'SRL» (7,1,2) (fixture s 3 18446744073709551615 63) =
 (let t := fixture s 3 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (63 : BitVec 64))).toNat), 7) (fixture s 3 18446744073709551615 63) = _
  have numeric : (((18446744073709551615 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (63 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_3_4_0
example (s : riscv_state) : «dfn'SRL» (0,1,2) (fixture s 3 2147483648 64) =
 (let t := fixture s 3 2147483648 64; t) := by
  change «write'GPR» (((2147483648 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (64 : BitVec 64))).toNat), 0) (fixture s 3 2147483648 64) = _
  have numeric : (((2147483648 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (64 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_3_4_1
example (s : riscv_state) : «dfn'SRL» (1,1,2) (fixture s 3 2147483648 64) =
 (let t := fixture s 3 2147483648 64; {t with c_gpr := holUpdate 7 (holUpdate 1 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((2147483648 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (64 : BitVec 64))).toNat), 1) (fixture s 3 2147483648 64) = _
  have numeric : (((2147483648 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (64 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_3_4_2
example (s : riscv_state) : «dfn'SRL» (2,1,2) (fixture s 3 2147483648 64) =
 (let t := fixture s 3 2147483648 64; {t with c_gpr := holUpdate 7 (holUpdate 2 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((2147483648 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (64 : BitVec 64))).toNat), 2) (fixture s 3 2147483648 64) = _
  have numeric : (((2147483648 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (64 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_3_4_7
example (s : riscv_state) : «dfn'SRL» (7,1,2) (fixture s 3 2147483648 64) =
 (let t := fixture s 3 2147483648 64; {t with c_gpr := holUpdate 7 (holUpdate 7 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((2147483648 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (64 : BitVec 64))).toNat), 7) (fixture s 3 2147483648 64) = _
  have numeric : (((2147483648 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (64 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_3_5_0
example (s : riscv_state) : «dfn'SRL» (0,1,2) (fixture s 3 4294967296 65) =
 (let t := fixture s 3 4294967296 65; t) := by
  change «write'GPR» (((4294967296 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (65 : BitVec 64))).toNat), 0) (fixture s 3 4294967296 65) = _
  have numeric : (((4294967296 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (65 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_3_5_1
example (s : riscv_state) : «dfn'SRL» (1,1,2) (fixture s 3 4294967296 65) =
 (let t := fixture s 3 4294967296 65; {t with c_gpr := holUpdate 7 (holUpdate 1 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((4294967296 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (65 : BitVec 64))).toNat), 1) (fixture s 3 4294967296 65) = _
  have numeric : (((4294967296 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (65 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_3_5_2
example (s : riscv_state) : «dfn'SRL» (2,1,2) (fixture s 3 4294967296 65) =
 (let t := fixture s 3 4294967296 65; {t with c_gpr := holUpdate 7 (holUpdate 2 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((4294967296 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (65 : BitVec 64))).toNat), 2) (fixture s 3 4294967296 65) = _
  have numeric : (((4294967296 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (65 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_3_5_7
example (s : riscv_state) : «dfn'SRL» (7,1,2) (fixture s 3 4294967296 65) =
 (let t := fixture s 3 4294967296 65; {t with c_gpr := holUpdate 7 (holUpdate 7 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((4294967296 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (65 : BitVec 64))).toNat), 7) (fixture s 3 4294967296 65) = _
  have numeric : (((4294967296 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (65 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_3_6_0
example (s : riscv_state) : «dfn'SRL» (0,1,2) (fixture s 3 9223372036854775809 127) =
 (let t := fixture s 3 9223372036854775809 127; t) := by
  change «write'GPR» (((9223372036854775809 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (127 : BitVec 64))).toNat), 0) (fixture s 3 9223372036854775809 127) = _
  have numeric : (((9223372036854775809 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (127 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_3_6_1
example (s : riscv_state) : «dfn'SRL» (1,1,2) (fixture s 3 9223372036854775809 127) =
 (let t := fixture s 3 9223372036854775809 127; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775809 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (127 : BitVec 64))).toNat), 1) (fixture s 3 9223372036854775809 127) = _
  have numeric : (((9223372036854775809 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (127 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_3_6_2
example (s : riscv_state) : «dfn'SRL» (2,1,2) (fixture s 3 9223372036854775809 127) =
 (let t := fixture s 3 9223372036854775809 127; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775809 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (127 : BitVec 64))).toNat), 2) (fixture s 3 9223372036854775809 127) = _
  have numeric : (((9223372036854775809 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (127 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_3_6_7
example (s : riscv_state) : «dfn'SRL» (7,1,2) (fixture s 3 9223372036854775809 127) =
 (let t := fixture s 3 9223372036854775809 127; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((9223372036854775809 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (127 : BitVec 64))).toNat), 7) (fixture s 3 9223372036854775809 127) = _
  have numeric : (((9223372036854775809 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (127 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_3_7_0
example (s : riscv_state) : «dfn'SRL» (0,1,2) (fixture s 3 17 129) =
 (let t := fixture s 3 17 129; t) := by
  change «write'GPR» (((17 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (129 : BitVec 64))).toNat), 0) (fixture s 3 17 129) = _
  have numeric : (((17 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (129 : BitVec 64))).toNat)) = (8 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_3_7_1
example (s : riscv_state) : «dfn'SRL» (1,1,2) (fixture s 3 17 129) =
 (let t := fixture s 3 17 129; {t with c_gpr := holUpdate 7 (holUpdate 1 8 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((17 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (129 : BitVec 64))).toNat), 1) (fixture s 3 17 129) = _
  have numeric : (((17 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (129 : BitVec 64))).toNat)) = (8 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_3_7_2
example (s : riscv_state) : «dfn'SRL» (2,1,2) (fixture s 3 17 129) =
 (let t := fixture s 3 17 129; {t with c_gpr := holUpdate 7 (holUpdate 2 8 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((17 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (129 : BitVec 64))).toNat), 2) (fixture s 3 17 129) = _
  have numeric : (((17 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (129 : BitVec 64))).toNat)) = (8 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_3_7_7
example (s : riscv_state) : «dfn'SRL» (7,1,2) (fixture s 3 17 129) =
 (let t := fixture s 3 17 129; {t with c_gpr := holUpdate 7 (holUpdate 7 8 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((17 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (129 : BitVec 64))).toNat), 7) (fixture s 3 17 129) = _
  have numeric : (((17 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (129 : BitVec 64))).toNat)) = (8 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_3_8_0
example (s : riscv_state) : «dfn'SRL» (0,0,2) (fixture s 3 17 31) =
 (let t := fixture s 3 17 31; t) := by
  change «write'GPR» (((0 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat), 0) (fixture s 3 17 31) = _
  have numeric : (((0 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_3_8_1
example (s : riscv_state) : «dfn'SRL» (1,0,2) (fixture s 3 17 31) =
 (let t := fixture s 3 17 31; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((0 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat), 1) (fixture s 3 17 31) = _
  have numeric : (((0 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_3_8_2
example (s : riscv_state) : «dfn'SRL» (2,0,2) (fixture s 3 17 31) =
 (let t := fixture s 3 17 31; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((0 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat), 2) (fixture s 3 17 31) = _
  have numeric : (((0 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_3_8_7
example (s : riscv_state) : «dfn'SRL» (7,0,2) (fixture s 3 17 31) =
 (let t := fixture s 3 17 31; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((0 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat), 7) (fixture s 3 17 31) = _
  have numeric : (((0 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_3_9_0
example (s : riscv_state) : «dfn'SRL» (0,1,0) (fixture s 3 18446744073709551615 63) =
 (let t := fixture s 3 18446744073709551615 63; t) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat), 0) (fixture s 3 18446744073709551615 63) = _
  have numeric : (((18446744073709551615 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_3_9_1
example (s : riscv_state) : «dfn'SRL» (1,1,0) (fixture s 3 18446744073709551615 63) =
 (let t := fixture s 3 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat), 1) (fixture s 3 18446744073709551615 63) = _
  have numeric : (((18446744073709551615 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_3_9_2
example (s : riscv_state) : «dfn'SRL» (2,1,0) (fixture s 3 18446744073709551615 63) =
 (let t := fixture s 3 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat), 2) (fixture s 3 18446744073709551615 63) = _
  have numeric : (((18446744073709551615 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRL_3_9_7
example (s : riscv_state) : «dfn'SRL» (7,1,0) (fixture s 3 18446744073709551615 63) =
 (let t := fixture s 3 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (((18446744073709551615 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat), 7) (fixture s 3 18446744073709551615 63) = _
  have numeric : (((18446744073709551615 : BitVec 64) >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_0_0_0
example (s : riscv_state) : «dfn'SRLW» (0,1,2) (fixture s 0 9223372036854775808 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775808 0) := by rfl

-- register_shift_SRLW_0_0_1
example (s : riscv_state) : «dfn'SRLW» (1,1,2) (fixture s 0 9223372036854775808 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775808 0) := by rfl

-- register_shift_SRLW_0_0_2
example (s : riscv_state) : «dfn'SRLW» (2,1,2) (fixture s 0 9223372036854775808 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775808 0) := by rfl

-- register_shift_SRLW_0_0_7
example (s : riscv_state) : «dfn'SRLW» (7,1,2) (fixture s 0 9223372036854775808 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775808 0) := by rfl

-- register_shift_SRLW_0_1_0
example (s : riscv_state) : «dfn'SRLW» (0,1,2) (fixture s 0 2147483649 31) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483649 31) := by rfl

-- register_shift_SRLW_0_1_1
example (s : riscv_state) : «dfn'SRLW» (1,1,2) (fixture s 0 2147483649 31) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483649 31) := by rfl

-- register_shift_SRLW_0_1_2
example (s : riscv_state) : «dfn'SRLW» (2,1,2) (fixture s 0 2147483649 31) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483649 31) := by rfl

-- register_shift_SRLW_0_1_7
example (s : riscv_state) : «dfn'SRLW» (7,1,2) (fixture s 0 2147483649 31) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483649 31) := by rfl

-- register_shift_SRLW_0_2_0
example (s : riscv_state) : «dfn'SRLW» (0,1,2) (fixture s 0 4294967297 32) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967297 32) := by rfl

-- register_shift_SRLW_0_2_1
example (s : riscv_state) : «dfn'SRLW» (1,1,2) (fixture s 0 4294967297 32) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967297 32) := by rfl

-- register_shift_SRLW_0_2_2
example (s : riscv_state) : «dfn'SRLW» (2,1,2) (fixture s 0 4294967297 32) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967297 32) := by rfl

-- register_shift_SRLW_0_2_7
example (s : riscv_state) : «dfn'SRLW» (7,1,2) (fixture s 0 4294967297 32) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967297 32) := by rfl

-- register_shift_SRLW_0_3_0
example (s : riscv_state) : «dfn'SRLW» (0,1,2) (fixture s 0 18446744073709551615 63) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 63) := by rfl

-- register_shift_SRLW_0_3_1
example (s : riscv_state) : «dfn'SRLW» (1,1,2) (fixture s 0 18446744073709551615 63) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 63) := by rfl

-- register_shift_SRLW_0_3_2
example (s : riscv_state) : «dfn'SRLW» (2,1,2) (fixture s 0 18446744073709551615 63) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 63) := by rfl

-- register_shift_SRLW_0_3_7
example (s : riscv_state) : «dfn'SRLW» (7,1,2) (fixture s 0 18446744073709551615 63) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 63) := by rfl

-- register_shift_SRLW_0_4_0
example (s : riscv_state) : «dfn'SRLW» (0,1,2) (fixture s 0 2147483648 64) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483648 64) := by rfl

-- register_shift_SRLW_0_4_1
example (s : riscv_state) : «dfn'SRLW» (1,1,2) (fixture s 0 2147483648 64) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483648 64) := by rfl

-- register_shift_SRLW_0_4_2
example (s : riscv_state) : «dfn'SRLW» (2,1,2) (fixture s 0 2147483648 64) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483648 64) := by rfl

-- register_shift_SRLW_0_4_7
example (s : riscv_state) : «dfn'SRLW» (7,1,2) (fixture s 0 2147483648 64) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483648 64) := by rfl

-- register_shift_SRLW_0_5_0
example (s : riscv_state) : «dfn'SRLW» (0,1,2) (fixture s 0 4294967296 65) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967296 65) := by rfl

-- register_shift_SRLW_0_5_1
example (s : riscv_state) : «dfn'SRLW» (1,1,2) (fixture s 0 4294967296 65) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967296 65) := by rfl

-- register_shift_SRLW_0_5_2
example (s : riscv_state) : «dfn'SRLW» (2,1,2) (fixture s 0 4294967296 65) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967296 65) := by rfl

-- register_shift_SRLW_0_5_7
example (s : riscv_state) : «dfn'SRLW» (7,1,2) (fixture s 0 4294967296 65) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967296 65) := by rfl

-- register_shift_SRLW_0_6_0
example (s : riscv_state) : «dfn'SRLW» (0,1,2) (fixture s 0 9223372036854775809 127) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775809 127) := by rfl

-- register_shift_SRLW_0_6_1
example (s : riscv_state) : «dfn'SRLW» (1,1,2) (fixture s 0 9223372036854775809 127) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775809 127) := by rfl

-- register_shift_SRLW_0_6_2
example (s : riscv_state) : «dfn'SRLW» (2,1,2) (fixture s 0 9223372036854775809 127) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775809 127) := by rfl

-- register_shift_SRLW_0_6_7
example (s : riscv_state) : «dfn'SRLW» (7,1,2) (fixture s 0 9223372036854775809 127) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775809 127) := by rfl

-- register_shift_SRLW_0_7_0
example (s : riscv_state) : «dfn'SRLW» (0,1,2) (fixture s 0 17 129) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 129) := by rfl

-- register_shift_SRLW_0_7_1
example (s : riscv_state) : «dfn'SRLW» (1,1,2) (fixture s 0 17 129) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 129) := by rfl

-- register_shift_SRLW_0_7_2
example (s : riscv_state) : «dfn'SRLW» (2,1,2) (fixture s 0 17 129) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 129) := by rfl

-- register_shift_SRLW_0_7_7
example (s : riscv_state) : «dfn'SRLW» (7,1,2) (fixture s 0 17 129) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 129) := by rfl

-- register_shift_SRLW_0_8_0
example (s : riscv_state) : «dfn'SRLW» (0,0,2) (fixture s 0 17 31) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 31) := by rfl

-- register_shift_SRLW_0_8_1
example (s : riscv_state) : «dfn'SRLW» (1,0,2) (fixture s 0 17 31) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 31) := by rfl

-- register_shift_SRLW_0_8_2
example (s : riscv_state) : «dfn'SRLW» (2,0,2) (fixture s 0 17 31) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 31) := by rfl

-- register_shift_SRLW_0_8_7
example (s : riscv_state) : «dfn'SRLW» (7,0,2) (fixture s 0 17 31) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 31) := by rfl

-- register_shift_SRLW_0_9_0
example (s : riscv_state) : «dfn'SRLW» (0,1,0) (fixture s 0 18446744073709551615 63) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 63) := by rfl

-- register_shift_SRLW_0_9_1
example (s : riscv_state) : «dfn'SRLW» (1,1,0) (fixture s 0 18446744073709551615 63) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 63) := by rfl

-- register_shift_SRLW_0_9_2
example (s : riscv_state) : «dfn'SRLW» (2,1,0) (fixture s 0 18446744073709551615 63) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 63) := by rfl

-- register_shift_SRLW_0_9_7
example (s : riscv_state) : «dfn'SRLW» (7,1,0) (fixture s 0 18446744073709551615 63) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 63) := by rfl

-- register_shift_SRLW_2_0_0
example (s : riscv_state) : «dfn'SRLW» (0,1,2) (fixture s 2 9223372036854775808 0) =
 (let t := fixture s 2 9223372036854775808 0; t) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 0) (fixture s 2 9223372036854775808 0) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_2_0_1
example (s : riscv_state) : «dfn'SRLW» (1,1,2) (fixture s 2 9223372036854775808 0) =
 (let t := fixture s 2 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 1) (fixture s 2 9223372036854775808 0) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_2_0_2
example (s : riscv_state) : «dfn'SRLW» (2,1,2) (fixture s 2 9223372036854775808 0) =
 (let t := fixture s 2 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 2) (fixture s 2 9223372036854775808 0) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_2_0_7
example (s : riscv_state) : «dfn'SRLW» (7,1,2) (fixture s 2 9223372036854775808 0) =
 (let t := fixture s 2 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 7) (fixture s 2 9223372036854775808 0) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_2_1_0
example (s : riscv_state) : «dfn'SRLW» (0,1,2) (fixture s 2 2147483649 31) =
 (let t := fixture s 2 2147483649 31; t) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483649 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 0) (fixture s 2 2147483649 31) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483649 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_2_1_1
example (s : riscv_state) : «dfn'SRLW» (1,1,2) (fixture s 2 2147483649 31) =
 (let t := fixture s 2 2147483649 31; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483649 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 1) (fixture s 2 2147483649 31) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483649 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_2_1_2
example (s : riscv_state) : «dfn'SRLW» (2,1,2) (fixture s 2 2147483649 31) =
 (let t := fixture s 2 2147483649 31; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483649 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 2) (fixture s 2 2147483649 31) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483649 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_2_1_7
example (s : riscv_state) : «dfn'SRLW» (7,1,2) (fixture s 2 2147483649 31) =
 (let t := fixture s 2 2147483649 31; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483649 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 7) (fixture s 2 2147483649 31) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483649 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_2_2_0
example (s : riscv_state) : «dfn'SRLW» (0,1,2) (fixture s 2 4294967297 32) =
 (let t := fixture s 2 4294967297 32; t) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967297 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat), 0) (fixture s 2 4294967297 32) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967297 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_2_2_1
example (s : riscv_state) : «dfn'SRLW» (1,1,2) (fixture s 2 4294967297 32) =
 (let t := fixture s 2 4294967297 32; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967297 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat), 1) (fixture s 2 4294967297 32) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967297 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_2_2_2
example (s : riscv_state) : «dfn'SRLW» (2,1,2) (fixture s 2 4294967297 32) =
 (let t := fixture s 2 4294967297 32; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967297 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat), 2) (fixture s 2 4294967297 32) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967297 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_2_2_7
example (s : riscv_state) : «dfn'SRLW» (7,1,2) (fixture s 2 4294967297 32) =
 (let t := fixture s 2 4294967297 32; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967297 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat), 7) (fixture s 2 4294967297 32) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967297 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_2_3_0
example (s : riscv_state) : «dfn'SRLW» (0,1,2) (fixture s 2 18446744073709551615 63) =
 (let t := fixture s 2 18446744073709551615 63; t) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat), 0) (fixture s 2 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_2_3_1
example (s : riscv_state) : «dfn'SRLW» (1,1,2) (fixture s 2 18446744073709551615 63) =
 (let t := fixture s 2 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat), 1) (fixture s 2 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_2_3_2
example (s : riscv_state) : «dfn'SRLW» (2,1,2) (fixture s 2 18446744073709551615 63) =
 (let t := fixture s 2 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat), 2) (fixture s 2 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_2_3_7
example (s : riscv_state) : «dfn'SRLW» (7,1,2) (fixture s 2 18446744073709551615 63) =
 (let t := fixture s 2 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat), 7) (fixture s 2 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_2_4_0
example (s : riscv_state) : «dfn'SRLW» (0,1,2) (fixture s 2 2147483648 64) =
 (let t := fixture s 2 2147483648 64; t) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483648 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat), 0) (fixture s 2 2147483648 64) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483648 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_2_4_1
example (s : riscv_state) : «dfn'SRLW» (1,1,2) (fixture s 2 2147483648 64) =
 (let t := fixture s 2 2147483648 64; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483648 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat), 1) (fixture s 2 2147483648 64) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483648 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_2_4_2
example (s : riscv_state) : «dfn'SRLW» (2,1,2) (fixture s 2 2147483648 64) =
 (let t := fixture s 2 2147483648 64; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483648 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat), 2) (fixture s 2 2147483648 64) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483648 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_2_4_7
example (s : riscv_state) : «dfn'SRLW» (7,1,2) (fixture s 2 2147483648 64) =
 (let t := fixture s 2 2147483648 64; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483648 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat), 7) (fixture s 2 2147483648 64) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483648 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_2_5_0
example (s : riscv_state) : «dfn'SRLW» (0,1,2) (fixture s 2 4294967296 65) =
 (let t := fixture s 2 4294967296 65; t) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967296 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat), 0) (fixture s 2 4294967296 65) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967296 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_2_5_1
example (s : riscv_state) : «dfn'SRLW» (1,1,2) (fixture s 2 4294967296 65) =
 (let t := fixture s 2 4294967296 65; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967296 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat), 1) (fixture s 2 4294967296 65) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967296 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_2_5_2
example (s : riscv_state) : «dfn'SRLW» (2,1,2) (fixture s 2 4294967296 65) =
 (let t := fixture s 2 4294967296 65; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967296 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat), 2) (fixture s 2 4294967296 65) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967296 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_2_5_7
example (s : riscv_state) : «dfn'SRLW» (7,1,2) (fixture s 2 4294967296 65) =
 (let t := fixture s 2 4294967296 65; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967296 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat), 7) (fixture s 2 4294967296 65) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967296 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_2_6_0
example (s : riscv_state) : «dfn'SRLW» (0,1,2) (fixture s 2 9223372036854775809 127) =
 (let t := fixture s 2 9223372036854775809 127; t) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat), 0) (fixture s 2 9223372036854775809 127) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_2_6_1
example (s : riscv_state) : «dfn'SRLW» (1,1,2) (fixture s 2 9223372036854775809 127) =
 (let t := fixture s 2 9223372036854775809 127; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat), 1) (fixture s 2 9223372036854775809 127) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_2_6_2
example (s : riscv_state) : «dfn'SRLW» (2,1,2) (fixture s 2 9223372036854775809 127) =
 (let t := fixture s 2 9223372036854775809 127; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat), 2) (fixture s 2 9223372036854775809 127) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_2_6_7
example (s : riscv_state) : «dfn'SRLW» (7,1,2) (fixture s 2 9223372036854775809 127) =
 (let t := fixture s 2 9223372036854775809 127; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat), 7) (fixture s 2 9223372036854775809 127) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_2_7_0
example (s : riscv_state) : «dfn'SRLW» (0,1,2) (fixture s 2 17 129) =
 (let t := fixture s 2 17 129; t) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (17 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat), 0) (fixture s 2 17 129) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (17 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat)) = (8 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_2_7_1
example (s : riscv_state) : «dfn'SRLW» (1,1,2) (fixture s 2 17 129) =
 (let t := fixture s 2 17 129; {t with c_gpr := holUpdate 7 (holUpdate 1 8 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (17 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat), 1) (fixture s 2 17 129) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (17 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat)) = (8 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_2_7_2
example (s : riscv_state) : «dfn'SRLW» (2,1,2) (fixture s 2 17 129) =
 (let t := fixture s 2 17 129; {t with c_gpr := holUpdate 7 (holUpdate 2 8 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (17 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat), 2) (fixture s 2 17 129) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (17 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat)) = (8 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_2_7_7
example (s : riscv_state) : «dfn'SRLW» (7,1,2) (fixture s 2 17 129) =
 (let t := fixture s 2 17 129; {t with c_gpr := holUpdate 7 (holUpdate 7 8 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (17 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat), 7) (fixture s 2 17 129) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (17 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat)) = (8 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_2_8_0
example (s : riscv_state) : «dfn'SRLW» (0,0,2) (fixture s 2 17 31) =
 (let t := fixture s 2 17 31; t) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (0 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 0) (fixture s 2 17 31) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (0 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_2_8_1
example (s : riscv_state) : «dfn'SRLW» (1,0,2) (fixture s 2 17 31) =
 (let t := fixture s 2 17 31; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (0 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 1) (fixture s 2 17 31) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (0 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_2_8_2
example (s : riscv_state) : «dfn'SRLW» (2,0,2) (fixture s 2 17 31) =
 (let t := fixture s 2 17 31; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (0 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 2) (fixture s 2 17 31) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (0 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_2_8_7
example (s : riscv_state) : «dfn'SRLW» (7,0,2) (fixture s 2 17 31) =
 (let t := fixture s 2 17 31; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (0 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 7) (fixture s 2 17 31) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (0 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_2_9_0
example (s : riscv_state) : «dfn'SRLW» (0,1,0) (fixture s 2 18446744073709551615 63) =
 (let t := fixture s 2 18446744073709551615 63; t) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 0) (fixture s 2 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_2_9_1
example (s : riscv_state) : «dfn'SRLW» (1,1,0) (fixture s 2 18446744073709551615 63) =
 (let t := fixture s 2 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 1) (fixture s 2 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_2_9_2
example (s : riscv_state) : «dfn'SRLW» (2,1,0) (fixture s 2 18446744073709551615 63) =
 (let t := fixture s 2 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 2) (fixture s 2 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_2_9_7
example (s : riscv_state) : «dfn'SRLW» (7,1,0) (fixture s 2 18446744073709551615 63) =
 (let t := fixture s 2 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 7) (fixture s 2 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_3_0_0
example (s : riscv_state) : «dfn'SRLW» (0,1,2) (fixture s 3 9223372036854775808 0) =
 (let t := fixture s 3 9223372036854775808 0; t) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 0) (fixture s 3 9223372036854775808 0) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_3_0_1
example (s : riscv_state) : «dfn'SRLW» (1,1,2) (fixture s 3 9223372036854775808 0) =
 (let t := fixture s 3 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 1) (fixture s 3 9223372036854775808 0) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_3_0_2
example (s : riscv_state) : «dfn'SRLW» (2,1,2) (fixture s 3 9223372036854775808 0) =
 (let t := fixture s 3 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 2) (fixture s 3 9223372036854775808 0) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_3_0_7
example (s : riscv_state) : «dfn'SRLW» (7,1,2) (fixture s 3 9223372036854775808 0) =
 (let t := fixture s 3 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 7) (fixture s 3 9223372036854775808 0) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_3_1_0
example (s : riscv_state) : «dfn'SRLW» (0,1,2) (fixture s 3 2147483649 31) =
 (let t := fixture s 3 2147483649 31; t) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483649 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 0) (fixture s 3 2147483649 31) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483649 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_3_1_1
example (s : riscv_state) : «dfn'SRLW» (1,1,2) (fixture s 3 2147483649 31) =
 (let t := fixture s 3 2147483649 31; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483649 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 1) (fixture s 3 2147483649 31) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483649 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_3_1_2
example (s : riscv_state) : «dfn'SRLW» (2,1,2) (fixture s 3 2147483649 31) =
 (let t := fixture s 3 2147483649 31; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483649 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 2) (fixture s 3 2147483649 31) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483649 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_3_1_7
example (s : riscv_state) : «dfn'SRLW» (7,1,2) (fixture s 3 2147483649 31) =
 (let t := fixture s 3 2147483649 31; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483649 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 7) (fixture s 3 2147483649 31) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483649 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_3_2_0
example (s : riscv_state) : «dfn'SRLW» (0,1,2) (fixture s 3 4294967297 32) =
 (let t := fixture s 3 4294967297 32; t) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967297 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat), 0) (fixture s 3 4294967297 32) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967297 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_3_2_1
example (s : riscv_state) : «dfn'SRLW» (1,1,2) (fixture s 3 4294967297 32) =
 (let t := fixture s 3 4294967297 32; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967297 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat), 1) (fixture s 3 4294967297 32) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967297 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_3_2_2
example (s : riscv_state) : «dfn'SRLW» (2,1,2) (fixture s 3 4294967297 32) =
 (let t := fixture s 3 4294967297 32; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967297 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat), 2) (fixture s 3 4294967297 32) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967297 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_3_2_7
example (s : riscv_state) : «dfn'SRLW» (7,1,2) (fixture s 3 4294967297 32) =
 (let t := fixture s 3 4294967297 32; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967297 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat), 7) (fixture s 3 4294967297 32) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967297 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_3_3_0
example (s : riscv_state) : «dfn'SRLW» (0,1,2) (fixture s 3 18446744073709551615 63) =
 (let t := fixture s 3 18446744073709551615 63; t) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat), 0) (fixture s 3 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_3_3_1
example (s : riscv_state) : «dfn'SRLW» (1,1,2) (fixture s 3 18446744073709551615 63) =
 (let t := fixture s 3 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat), 1) (fixture s 3 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_3_3_2
example (s : riscv_state) : «dfn'SRLW» (2,1,2) (fixture s 3 18446744073709551615 63) =
 (let t := fixture s 3 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat), 2) (fixture s 3 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_3_3_7
example (s : riscv_state) : «dfn'SRLW» (7,1,2) (fixture s 3 18446744073709551615 63) =
 (let t := fixture s 3 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat), 7) (fixture s 3 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_3_4_0
example (s : riscv_state) : «dfn'SRLW» (0,1,2) (fixture s 3 2147483648 64) =
 (let t := fixture s 3 2147483648 64; t) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483648 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat), 0) (fixture s 3 2147483648 64) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483648 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_3_4_1
example (s : riscv_state) : «dfn'SRLW» (1,1,2) (fixture s 3 2147483648 64) =
 (let t := fixture s 3 2147483648 64; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483648 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat), 1) (fixture s 3 2147483648 64) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483648 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_3_4_2
example (s : riscv_state) : «dfn'SRLW» (2,1,2) (fixture s 3 2147483648 64) =
 (let t := fixture s 3 2147483648 64; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483648 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat), 2) (fixture s 3 2147483648 64) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483648 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_3_4_7
example (s : riscv_state) : «dfn'SRLW» (7,1,2) (fixture s 3 2147483648 64) =
 (let t := fixture s 3 2147483648 64; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483648 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat), 7) (fixture s 3 2147483648 64) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (2147483648 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_3_5_0
example (s : riscv_state) : «dfn'SRLW» (0,1,2) (fixture s 3 4294967296 65) =
 (let t := fixture s 3 4294967296 65; t) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967296 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat), 0) (fixture s 3 4294967296 65) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967296 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_3_5_1
example (s : riscv_state) : «dfn'SRLW» (1,1,2) (fixture s 3 4294967296 65) =
 (let t := fixture s 3 4294967296 65; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967296 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat), 1) (fixture s 3 4294967296 65) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967296 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_3_5_2
example (s : riscv_state) : «dfn'SRLW» (2,1,2) (fixture s 3 4294967296 65) =
 (let t := fixture s 3 4294967296 65; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967296 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat), 2) (fixture s 3 4294967296 65) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967296 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_3_5_7
example (s : riscv_state) : «dfn'SRLW» (7,1,2) (fixture s 3 4294967296 65) =
 (let t := fixture s 3 4294967296 65; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967296 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat), 7) (fixture s 3 4294967296 65) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (4294967296 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_3_6_0
example (s : riscv_state) : «dfn'SRLW» (0,1,2) (fixture s 3 9223372036854775809 127) =
 (let t := fixture s 3 9223372036854775809 127; t) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat), 0) (fixture s 3 9223372036854775809 127) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_3_6_1
example (s : riscv_state) : «dfn'SRLW» (1,1,2) (fixture s 3 9223372036854775809 127) =
 (let t := fixture s 3 9223372036854775809 127; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat), 1) (fixture s 3 9223372036854775809 127) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_3_6_2
example (s : riscv_state) : «dfn'SRLW» (2,1,2) (fixture s 3 9223372036854775809 127) =
 (let t := fixture s 3 9223372036854775809 127; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat), 2) (fixture s 3 9223372036854775809 127) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_3_6_7
example (s : riscv_state) : «dfn'SRLW» (7,1,2) (fixture s 3 9223372036854775809 127) =
 (let t := fixture s 3 9223372036854775809 127; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat), 7) (fixture s 3 9223372036854775809 127) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_3_7_0
example (s : riscv_state) : «dfn'SRLW» (0,1,2) (fixture s 3 17 129) =
 (let t := fixture s 3 17 129; t) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (17 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat), 0) (fixture s 3 17 129) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (17 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat)) = (8 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_3_7_1
example (s : riscv_state) : «dfn'SRLW» (1,1,2) (fixture s 3 17 129) =
 (let t := fixture s 3 17 129; {t with c_gpr := holUpdate 7 (holUpdate 1 8 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (17 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat), 1) (fixture s 3 17 129) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (17 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat)) = (8 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_3_7_2
example (s : riscv_state) : «dfn'SRLW» (2,1,2) (fixture s 3 17 129) =
 (let t := fixture s 3 17 129; {t with c_gpr := holUpdate 7 (holUpdate 2 8 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (17 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat), 2) (fixture s 3 17 129) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (17 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat)) = (8 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_3_7_7
example (s : riscv_state) : «dfn'SRLW» (7,1,2) (fixture s 3 17 129) =
 (let t := fixture s 3 17 129; {t with c_gpr := holUpdate 7 (holUpdate 7 8 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (17 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat), 7) (fixture s 3 17 129) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (17 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat)) = (8 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_3_8_0
example (s : riscv_state) : «dfn'SRLW» (0,0,2) (fixture s 3 17 31) =
 (let t := fixture s 3 17 31; t) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (0 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 0) (fixture s 3 17 31) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (0 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_3_8_1
example (s : riscv_state) : «dfn'SRLW» (1,0,2) (fixture s 3 17 31) =
 (let t := fixture s 3 17 31; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (0 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 1) (fixture s 3 17 31) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (0 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_3_8_2
example (s : riscv_state) : «dfn'SRLW» (2,0,2) (fixture s 3 17 31) =
 (let t := fixture s 3 17 31; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (0 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 2) (fixture s 3 17 31) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (0 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_3_8_7
example (s : riscv_state) : «dfn'SRLW» (7,0,2) (fixture s 3 17 31) =
 (let t := fixture s 3 17 31; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (0 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 7) (fixture s 3 17 31) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (0 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_3_9_0
example (s : riscv_state) : «dfn'SRLW» (0,1,0) (fixture s 3 18446744073709551615 63) =
 (let t := fixture s 3 18446744073709551615 63; t) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 0) (fixture s 3 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_3_9_1
example (s : riscv_state) : «dfn'SRLW» (1,1,0) (fixture s 3 18446744073709551615 63) =
 (let t := fixture s 3 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 1) (fixture s 3 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_3_9_2
example (s : riscv_state) : «dfn'SRLW» (2,1,0) (fixture s 3 18446744073709551615 63) =
 (let t := fixture s 3 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 2) (fixture s 3 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRLW_3_9_7
example (s : riscv_state) : «dfn'SRLW» (7,1,0) (fixture s 3 18446744073709551615 63) =
 (let t := fixture s 3 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 7) (fixture s 3 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 ((holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) >>> (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_0_0_0
example (s : riscv_state) : «dfn'SRA» (0,1,2) (fixture s 0 9223372036854775808 0) =
 (let t := fixture s 0 9223372036854775808 0; t) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 0) (fixture s 0 9223372036854775808 0) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_0_0_1
example (s : riscv_state) : «dfn'SRA» (1,1,2) (fixture s 0 9223372036854775808 0) =
 (let t := fixture s 0 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 1) (fixture s 0 9223372036854775808 0) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_0_0_2
example (s : riscv_state) : «dfn'SRA» (2,1,2) (fixture s 0 9223372036854775808 0) =
 (let t := fixture s 0 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 2) (fixture s 0 9223372036854775808 0) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_0_0_7
example (s : riscv_state) : «dfn'SRA» (7,1,2) (fixture s 0 9223372036854775808 0) =
 (let t := fixture s 0 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 7) (fixture s 0 9223372036854775808 0) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_0_1_0
example (s : riscv_state) : «dfn'SRA» (0,1,2) (fixture s 0 2147483649 31) =
 (let t := fixture s 0 2147483649 31; t) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (2147483649 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 0) (fixture s 0 2147483649 31) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (2147483649 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_0_1_1
example (s : riscv_state) : «dfn'SRA» (1,1,2) (fixture s 0 2147483649 31) =
 (let t := fixture s 0 2147483649 31; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (2147483649 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 1) (fixture s 0 2147483649 31) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (2147483649 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_0_1_2
example (s : riscv_state) : «dfn'SRA» (2,1,2) (fixture s 0 2147483649 31) =
 (let t := fixture s 0 2147483649 31; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (2147483649 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 2) (fixture s 0 2147483649 31) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (2147483649 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_0_1_7
example (s : riscv_state) : «dfn'SRA» (7,1,2) (fixture s 0 2147483649 31) =
 (let t := fixture s 0 2147483649 31; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (2147483649 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 7) (fixture s 0 2147483649 31) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (2147483649 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_0_2_0
example (s : riscv_state) : «dfn'SRA» (0,1,2) (fixture s 0 4294967297 32) =
 (let t := fixture s 0 4294967297 32; t) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (4294967297 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat), 0) (fixture s 0 4294967297 32) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (4294967297 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_0_2_1
example (s : riscv_state) : «dfn'SRA» (1,1,2) (fixture s 0 4294967297 32) =
 (let t := fixture s 0 4294967297 32; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (4294967297 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat), 1) (fixture s 0 4294967297 32) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (4294967297 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_0_2_2
example (s : riscv_state) : «dfn'SRA» (2,1,2) (fixture s 0 4294967297 32) =
 (let t := fixture s 0 4294967297 32; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (4294967297 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat), 2) (fixture s 0 4294967297 32) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (4294967297 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_0_2_7
example (s : riscv_state) : «dfn'SRA» (7,1,2) (fixture s 0 4294967297 32) =
 (let t := fixture s 0 4294967297 32; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (4294967297 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat), 7) (fixture s 0 4294967297 32) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (4294967297 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_0_3_0
example (s : riscv_state) : «dfn'SRA» (0,1,2) (fixture s 0 18446744073709551615 63) =
 (let t := fixture s 0 18446744073709551615 63; t) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat), 0) (fixture s 0 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_0_3_1
example (s : riscv_state) : «dfn'SRA» (1,1,2) (fixture s 0 18446744073709551615 63) =
 (let t := fixture s 0 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat), 1) (fixture s 0 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_0_3_2
example (s : riscv_state) : «dfn'SRA» (2,1,2) (fixture s 0 18446744073709551615 63) =
 (let t := fixture s 0 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat), 2) (fixture s 0 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_0_3_7
example (s : riscv_state) : «dfn'SRA» (7,1,2) (fixture s 0 18446744073709551615 63) =
 (let t := fixture s 0 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat), 7) (fixture s 0 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_0_4_0
example (s : riscv_state) : «dfn'SRA» (0,1,2) (fixture s 0 2147483648 64) =
 (let t := fixture s 0 2147483648 64; t) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (2147483648 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat), 0) (fixture s 0 2147483648 64) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (2147483648 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_0_4_1
example (s : riscv_state) : «dfn'SRA» (1,1,2) (fixture s 0 2147483648 64) =
 (let t := fixture s 0 2147483648 64; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (2147483648 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat), 1) (fixture s 0 2147483648 64) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (2147483648 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_0_4_2
example (s : riscv_state) : «dfn'SRA» (2,1,2) (fixture s 0 2147483648 64) =
 (let t := fixture s 0 2147483648 64; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (2147483648 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat), 2) (fixture s 0 2147483648 64) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (2147483648 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_0_4_7
example (s : riscv_state) : «dfn'SRA» (7,1,2) (fixture s 0 2147483648 64) =
 (let t := fixture s 0 2147483648 64; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (2147483648 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat), 7) (fixture s 0 2147483648 64) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (2147483648 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_0_5_0
example (s : riscv_state) : «dfn'SRA» (0,1,2) (fixture s 0 4294967296 65) =
 (let t := fixture s 0 4294967296 65; t) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (4294967296 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat), 0) (fixture s 0 4294967296 65) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (4294967296 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_0_5_1
example (s : riscv_state) : «dfn'SRA» (1,1,2) (fixture s 0 4294967296 65) =
 (let t := fixture s 0 4294967296 65; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (4294967296 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat), 1) (fixture s 0 4294967296 65) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (4294967296 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_0_5_2
example (s : riscv_state) : «dfn'SRA» (2,1,2) (fixture s 0 4294967296 65) =
 (let t := fixture s 0 4294967296 65; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (4294967296 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat), 2) (fixture s 0 4294967296 65) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (4294967296 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_0_5_7
example (s : riscv_state) : «dfn'SRA» (7,1,2) (fixture s 0 4294967296 65) =
 (let t := fixture s 0 4294967296 65; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (4294967296 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat), 7) (fixture s 0 4294967296 65) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (4294967296 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_0_6_0
example (s : riscv_state) : «dfn'SRA» (0,1,2) (fixture s 0 9223372036854775809 127) =
 (let t := fixture s 0 9223372036854775809 127; t) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat), 0) (fixture s 0 9223372036854775809 127) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_0_6_1
example (s : riscv_state) : «dfn'SRA» (1,1,2) (fixture s 0 9223372036854775809 127) =
 (let t := fixture s 0 9223372036854775809 127; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat), 1) (fixture s 0 9223372036854775809 127) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_0_6_2
example (s : riscv_state) : «dfn'SRA» (2,1,2) (fixture s 0 9223372036854775809 127) =
 (let t := fixture s 0 9223372036854775809 127; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat), 2) (fixture s 0 9223372036854775809 127) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_0_6_7
example (s : riscv_state) : «dfn'SRA» (7,1,2) (fixture s 0 9223372036854775809 127) =
 (let t := fixture s 0 9223372036854775809 127; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat), 7) (fixture s 0 9223372036854775809 127) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_0_7_0
example (s : riscv_state) : «dfn'SRA» (0,1,2) (fixture s 0 17 129) =
 (let t := fixture s 0 17 129; t) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (17 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat), 0) (fixture s 0 17 129) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (17 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat)) = (8 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_0_7_1
example (s : riscv_state) : «dfn'SRA» (1,1,2) (fixture s 0 17 129) =
 (let t := fixture s 0 17 129; {t with c_gpr := holUpdate 7 (holUpdate 1 8 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (17 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat), 1) (fixture s 0 17 129) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (17 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat)) = (8 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_0_7_2
example (s : riscv_state) : «dfn'SRA» (2,1,2) (fixture s 0 17 129) =
 (let t := fixture s 0 17 129; {t with c_gpr := holUpdate 7 (holUpdate 2 8 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (17 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat), 2) (fixture s 0 17 129) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (17 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat)) = (8 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_0_7_7
example (s : riscv_state) : «dfn'SRA» (7,1,2) (fixture s 0 17 129) =
 (let t := fixture s 0 17 129; {t with c_gpr := holUpdate 7 (holUpdate 7 8 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (17 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat), 7) (fixture s 0 17 129) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (17 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat)) = (8 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_0_8_0
example (s : riscv_state) : «dfn'SRA» (0,0,2) (fixture s 0 17 31) =
 (let t := fixture s 0 17 31; t) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (0 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 0) (fixture s 0 17 31) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (0 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_0_8_1
example (s : riscv_state) : «dfn'SRA» (1,0,2) (fixture s 0 17 31) =
 (let t := fixture s 0 17 31; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (0 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 1) (fixture s 0 17 31) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (0 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_0_8_2
example (s : riscv_state) : «dfn'SRA» (2,0,2) (fixture s 0 17 31) =
 (let t := fixture s 0 17 31; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (0 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 2) (fixture s 0 17 31) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (0 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_0_8_7
example (s : riscv_state) : «dfn'SRA» (7,0,2) (fixture s 0 17 31) =
 (let t := fixture s 0 17 31; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (0 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 7) (fixture s 0 17 31) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (0 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_0_9_0
example (s : riscv_state) : «dfn'SRA» (0,1,0) (fixture s 0 18446744073709551615 63) =
 (let t := fixture s 0 18446744073709551615 63; t) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 0) (fixture s 0 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_0_9_1
example (s : riscv_state) : «dfn'SRA» (1,1,0) (fixture s 0 18446744073709551615 63) =
 (let t := fixture s 0 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 1) (fixture s 0 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_0_9_2
example (s : riscv_state) : «dfn'SRA» (2,1,0) (fixture s 0 18446744073709551615 63) =
 (let t := fixture s 0 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 2) (fixture s 0 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_0_9_7
example (s : riscv_state) : «dfn'SRA» (7,1,0) (fixture s 0 18446744073709551615 63) =
 (let t := fixture s 0 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 7) (fixture s 0 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_2_0_0
example (s : riscv_state) : «dfn'SRA» (0,1,2) (fixture s 2 9223372036854775808 0) =
 (let t := fixture s 2 9223372036854775808 0; t) := by
  change «write'GPR» ((BitVec.sshiftRight (9223372036854775808 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat), 0) (fixture s 2 9223372036854775808 0) = _
  have numeric : ((BitVec.sshiftRight (9223372036854775808 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_2_0_1
example (s : riscv_state) : «dfn'SRA» (1,1,2) (fixture s 2 9223372036854775808 0) =
 (let t := fixture s 2 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 1 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (9223372036854775808 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat), 1) (fixture s 2 9223372036854775808 0) = _
  have numeric : ((BitVec.sshiftRight (9223372036854775808 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_2_0_2
example (s : riscv_state) : «dfn'SRA» (2,1,2) (fixture s 2 9223372036854775808 0) =
 (let t := fixture s 2 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 2 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (9223372036854775808 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat), 2) (fixture s 2 9223372036854775808 0) = _
  have numeric : ((BitVec.sshiftRight (9223372036854775808 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_2_0_7
example (s : riscv_state) : «dfn'SRA» (7,1,2) (fixture s 2 9223372036854775808 0) =
 (let t := fixture s 2 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 7 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (9223372036854775808 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat), 7) (fixture s 2 9223372036854775808 0) = _
  have numeric : ((BitVec.sshiftRight (9223372036854775808 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_2_1_0
example (s : riscv_state) : «dfn'SRA» (0,1,2) (fixture s 2 2147483649 31) =
 (let t := fixture s 2 2147483649 31; t) := by
  change «write'GPR» ((BitVec.sshiftRight (2147483649 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat), 0) (fixture s 2 2147483649 31) = _
  have numeric : ((BitVec.sshiftRight (2147483649 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_2_1_1
example (s : riscv_state) : «dfn'SRA» (1,1,2) (fixture s 2 2147483649 31) =
 (let t := fixture s 2 2147483649 31; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (2147483649 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat), 1) (fixture s 2 2147483649 31) = _
  have numeric : ((BitVec.sshiftRight (2147483649 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_2_1_2
example (s : riscv_state) : «dfn'SRA» (2,1,2) (fixture s 2 2147483649 31) =
 (let t := fixture s 2 2147483649 31; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (2147483649 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat), 2) (fixture s 2 2147483649 31) = _
  have numeric : ((BitVec.sshiftRight (2147483649 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_2_1_7
example (s : riscv_state) : «dfn'SRA» (7,1,2) (fixture s 2 2147483649 31) =
 (let t := fixture s 2 2147483649 31; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (2147483649 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat), 7) (fixture s 2 2147483649 31) = _
  have numeric : ((BitVec.sshiftRight (2147483649 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_2_2_0
example (s : riscv_state) : «dfn'SRA» (0,1,2) (fixture s 2 4294967297 32) =
 (let t := fixture s 2 4294967297 32; t) := by
  change «write'GPR» ((BitVec.sshiftRight (4294967297 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (32 : BitVec 64))).toNat), 0) (fixture s 2 4294967297 32) = _
  have numeric : ((BitVec.sshiftRight (4294967297 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (32 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_2_2_1
example (s : riscv_state) : «dfn'SRA» (1,1,2) (fixture s 2 4294967297 32) =
 (let t := fixture s 2 4294967297 32; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (4294967297 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (32 : BitVec 64))).toNat), 1) (fixture s 2 4294967297 32) = _
  have numeric : ((BitVec.sshiftRight (4294967297 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (32 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_2_2_2
example (s : riscv_state) : «dfn'SRA» (2,1,2) (fixture s 2 4294967297 32) =
 (let t := fixture s 2 4294967297 32; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (4294967297 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (32 : BitVec 64))).toNat), 2) (fixture s 2 4294967297 32) = _
  have numeric : ((BitVec.sshiftRight (4294967297 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (32 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_2_2_7
example (s : riscv_state) : «dfn'SRA» (7,1,2) (fixture s 2 4294967297 32) =
 (let t := fixture s 2 4294967297 32; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (4294967297 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (32 : BitVec 64))).toNat), 7) (fixture s 2 4294967297 32) = _
  have numeric : ((BitVec.sshiftRight (4294967297 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (32 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_2_3_0
example (s : riscv_state) : «dfn'SRA» (0,1,2) (fixture s 2 18446744073709551615 63) =
 (let t := fixture s 2 18446744073709551615 63; t) := by
  change «write'GPR» ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (63 : BitVec 64))).toNat), 0) (fixture s 2 18446744073709551615 63) = _
  have numeric : ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (63 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_2_3_1
example (s : riscv_state) : «dfn'SRA» (1,1,2) (fixture s 2 18446744073709551615 63) =
 (let t := fixture s 2 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (63 : BitVec 64))).toNat), 1) (fixture s 2 18446744073709551615 63) = _
  have numeric : ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (63 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_2_3_2
example (s : riscv_state) : «dfn'SRA» (2,1,2) (fixture s 2 18446744073709551615 63) =
 (let t := fixture s 2 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (63 : BitVec 64))).toNat), 2) (fixture s 2 18446744073709551615 63) = _
  have numeric : ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (63 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_2_3_7
example (s : riscv_state) : «dfn'SRA» (7,1,2) (fixture s 2 18446744073709551615 63) =
 (let t := fixture s 2 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (63 : BitVec 64))).toNat), 7) (fixture s 2 18446744073709551615 63) = _
  have numeric : ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (63 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_2_4_0
example (s : riscv_state) : «dfn'SRA» (0,1,2) (fixture s 2 2147483648 64) =
 (let t := fixture s 2 2147483648 64; t) := by
  change «write'GPR» ((BitVec.sshiftRight (2147483648 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (64 : BitVec 64))).toNat), 0) (fixture s 2 2147483648 64) = _
  have numeric : ((BitVec.sshiftRight (2147483648 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (64 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_2_4_1
example (s : riscv_state) : «dfn'SRA» (1,1,2) (fixture s 2 2147483648 64) =
 (let t := fixture s 2 2147483648 64; {t with c_gpr := holUpdate 7 (holUpdate 1 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (2147483648 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (64 : BitVec 64))).toNat), 1) (fixture s 2 2147483648 64) = _
  have numeric : ((BitVec.sshiftRight (2147483648 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (64 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_2_4_2
example (s : riscv_state) : «dfn'SRA» (2,1,2) (fixture s 2 2147483648 64) =
 (let t := fixture s 2 2147483648 64; {t with c_gpr := holUpdate 7 (holUpdate 2 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (2147483648 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (64 : BitVec 64))).toNat), 2) (fixture s 2 2147483648 64) = _
  have numeric : ((BitVec.sshiftRight (2147483648 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (64 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_2_4_7
example (s : riscv_state) : «dfn'SRA» (7,1,2) (fixture s 2 2147483648 64) =
 (let t := fixture s 2 2147483648 64; {t with c_gpr := holUpdate 7 (holUpdate 7 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (2147483648 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (64 : BitVec 64))).toNat), 7) (fixture s 2 2147483648 64) = _
  have numeric : ((BitVec.sshiftRight (2147483648 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (64 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_2_5_0
example (s : riscv_state) : «dfn'SRA» (0,1,2) (fixture s 2 4294967296 65) =
 (let t := fixture s 2 4294967296 65; t) := by
  change «write'GPR» ((BitVec.sshiftRight (4294967296 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (65 : BitVec 64))).toNat), 0) (fixture s 2 4294967296 65) = _
  have numeric : ((BitVec.sshiftRight (4294967296 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (65 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_2_5_1
example (s : riscv_state) : «dfn'SRA» (1,1,2) (fixture s 2 4294967296 65) =
 (let t := fixture s 2 4294967296 65; {t with c_gpr := holUpdate 7 (holUpdate 1 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (4294967296 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (65 : BitVec 64))).toNat), 1) (fixture s 2 4294967296 65) = _
  have numeric : ((BitVec.sshiftRight (4294967296 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (65 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_2_5_2
example (s : riscv_state) : «dfn'SRA» (2,1,2) (fixture s 2 4294967296 65) =
 (let t := fixture s 2 4294967296 65; {t with c_gpr := holUpdate 7 (holUpdate 2 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (4294967296 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (65 : BitVec 64))).toNat), 2) (fixture s 2 4294967296 65) = _
  have numeric : ((BitVec.sshiftRight (4294967296 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (65 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_2_5_7
example (s : riscv_state) : «dfn'SRA» (7,1,2) (fixture s 2 4294967296 65) =
 (let t := fixture s 2 4294967296 65; {t with c_gpr := holUpdate 7 (holUpdate 7 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (4294967296 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (65 : BitVec 64))).toNat), 7) (fixture s 2 4294967296 65) = _
  have numeric : ((BitVec.sshiftRight (4294967296 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (65 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_2_6_0
example (s : riscv_state) : «dfn'SRA» (0,1,2) (fixture s 2 9223372036854775809 127) =
 (let t := fixture s 2 9223372036854775809 127; t) := by
  change «write'GPR» ((BitVec.sshiftRight (9223372036854775809 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (127 : BitVec 64))).toNat), 0) (fixture s 2 9223372036854775809 127) = _
  have numeric : ((BitVec.sshiftRight (9223372036854775809 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (127 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_2_6_1
example (s : riscv_state) : «dfn'SRA» (1,1,2) (fixture s 2 9223372036854775809 127) =
 (let t := fixture s 2 9223372036854775809 127; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (9223372036854775809 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (127 : BitVec 64))).toNat), 1) (fixture s 2 9223372036854775809 127) = _
  have numeric : ((BitVec.sshiftRight (9223372036854775809 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (127 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_2_6_2
example (s : riscv_state) : «dfn'SRA» (2,1,2) (fixture s 2 9223372036854775809 127) =
 (let t := fixture s 2 9223372036854775809 127; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (9223372036854775809 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (127 : BitVec 64))).toNat), 2) (fixture s 2 9223372036854775809 127) = _
  have numeric : ((BitVec.sshiftRight (9223372036854775809 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (127 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_2_6_7
example (s : riscv_state) : «dfn'SRA» (7,1,2) (fixture s 2 9223372036854775809 127) =
 (let t := fixture s 2 9223372036854775809 127; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (9223372036854775809 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (127 : BitVec 64))).toNat), 7) (fixture s 2 9223372036854775809 127) = _
  have numeric : ((BitVec.sshiftRight (9223372036854775809 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (127 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_2_7_0
example (s : riscv_state) : «dfn'SRA» (0,1,2) (fixture s 2 17 129) =
 (let t := fixture s 2 17 129; t) := by
  change «write'GPR» ((BitVec.sshiftRight (17 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (129 : BitVec 64))).toNat), 0) (fixture s 2 17 129) = _
  have numeric : ((BitVec.sshiftRight (17 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (129 : BitVec 64))).toNat)) = (8 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_2_7_1
example (s : riscv_state) : «dfn'SRA» (1,1,2) (fixture s 2 17 129) =
 (let t := fixture s 2 17 129; {t with c_gpr := holUpdate 7 (holUpdate 1 8 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (17 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (129 : BitVec 64))).toNat), 1) (fixture s 2 17 129) = _
  have numeric : ((BitVec.sshiftRight (17 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (129 : BitVec 64))).toNat)) = (8 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_2_7_2
example (s : riscv_state) : «dfn'SRA» (2,1,2) (fixture s 2 17 129) =
 (let t := fixture s 2 17 129; {t with c_gpr := holUpdate 7 (holUpdate 2 8 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (17 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (129 : BitVec 64))).toNat), 2) (fixture s 2 17 129) = _
  have numeric : ((BitVec.sshiftRight (17 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (129 : BitVec 64))).toNat)) = (8 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_2_7_7
example (s : riscv_state) : «dfn'SRA» (7,1,2) (fixture s 2 17 129) =
 (let t := fixture s 2 17 129; {t with c_gpr := holUpdate 7 (holUpdate 7 8 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (17 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (129 : BitVec 64))).toNat), 7) (fixture s 2 17 129) = _
  have numeric : ((BitVec.sshiftRight (17 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (129 : BitVec 64))).toNat)) = (8 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_2_8_0
example (s : riscv_state) : «dfn'SRA» (0,0,2) (fixture s 2 17 31) =
 (let t := fixture s 2 17 31; t) := by
  change «write'GPR» ((BitVec.sshiftRight (0 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat), 0) (fixture s 2 17 31) = _
  have numeric : ((BitVec.sshiftRight (0 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_2_8_1
example (s : riscv_state) : «dfn'SRA» (1,0,2) (fixture s 2 17 31) =
 (let t := fixture s 2 17 31; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (0 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat), 1) (fixture s 2 17 31) = _
  have numeric : ((BitVec.sshiftRight (0 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_2_8_2
example (s : riscv_state) : «dfn'SRA» (2,0,2) (fixture s 2 17 31) =
 (let t := fixture s 2 17 31; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (0 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat), 2) (fixture s 2 17 31) = _
  have numeric : ((BitVec.sshiftRight (0 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_2_8_7
example (s : riscv_state) : «dfn'SRA» (7,0,2) (fixture s 2 17 31) =
 (let t := fixture s 2 17 31; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (0 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat), 7) (fixture s 2 17 31) = _
  have numeric : ((BitVec.sshiftRight (0 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_2_9_0
example (s : riscv_state) : «dfn'SRA» (0,1,0) (fixture s 2 18446744073709551615 63) =
 (let t := fixture s 2 18446744073709551615 63; t) := by
  change «write'GPR» ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat), 0) (fixture s 2 18446744073709551615 63) = _
  have numeric : ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_2_9_1
example (s : riscv_state) : «dfn'SRA» (1,1,0) (fixture s 2 18446744073709551615 63) =
 (let t := fixture s 2 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat), 1) (fixture s 2 18446744073709551615 63) = _
  have numeric : ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_2_9_2
example (s : riscv_state) : «dfn'SRA» (2,1,0) (fixture s 2 18446744073709551615 63) =
 (let t := fixture s 2 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat), 2) (fixture s 2 18446744073709551615 63) = _
  have numeric : ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_2_9_7
example (s : riscv_state) : «dfn'SRA» (7,1,0) (fixture s 2 18446744073709551615 63) =
 (let t := fixture s 2 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat), 7) (fixture s 2 18446744073709551615 63) = _
  have numeric : ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_3_0_0
example (s : riscv_state) : «dfn'SRA» (0,1,2) (fixture s 3 9223372036854775808 0) =
 (let t := fixture s 3 9223372036854775808 0; t) := by
  change «write'GPR» ((BitVec.sshiftRight (9223372036854775808 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat), 0) (fixture s 3 9223372036854775808 0) = _
  have numeric : ((BitVec.sshiftRight (9223372036854775808 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_3_0_1
example (s : riscv_state) : «dfn'SRA» (1,1,2) (fixture s 3 9223372036854775808 0) =
 (let t := fixture s 3 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 1 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (9223372036854775808 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat), 1) (fixture s 3 9223372036854775808 0) = _
  have numeric : ((BitVec.sshiftRight (9223372036854775808 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_3_0_2
example (s : riscv_state) : «dfn'SRA» (2,1,2) (fixture s 3 9223372036854775808 0) =
 (let t := fixture s 3 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 2 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (9223372036854775808 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat), 2) (fixture s 3 9223372036854775808 0) = _
  have numeric : ((BitVec.sshiftRight (9223372036854775808 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_3_0_7
example (s : riscv_state) : «dfn'SRA» (7,1,2) (fixture s 3 9223372036854775808 0) =
 (let t := fixture s 3 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 7 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (9223372036854775808 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat), 7) (fixture s 3 9223372036854775808 0) = _
  have numeric : ((BitVec.sshiftRight (9223372036854775808 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat)) = (9223372036854775808 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_3_1_0
example (s : riscv_state) : «dfn'SRA» (0,1,2) (fixture s 3 2147483649 31) =
 (let t := fixture s 3 2147483649 31; t) := by
  change «write'GPR» ((BitVec.sshiftRight (2147483649 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat), 0) (fixture s 3 2147483649 31) = _
  have numeric : ((BitVec.sshiftRight (2147483649 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_3_1_1
example (s : riscv_state) : «dfn'SRA» (1,1,2) (fixture s 3 2147483649 31) =
 (let t := fixture s 3 2147483649 31; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (2147483649 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat), 1) (fixture s 3 2147483649 31) = _
  have numeric : ((BitVec.sshiftRight (2147483649 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_3_1_2
example (s : riscv_state) : «dfn'SRA» (2,1,2) (fixture s 3 2147483649 31) =
 (let t := fixture s 3 2147483649 31; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (2147483649 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat), 2) (fixture s 3 2147483649 31) = _
  have numeric : ((BitVec.sshiftRight (2147483649 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_3_1_7
example (s : riscv_state) : «dfn'SRA» (7,1,2) (fixture s 3 2147483649 31) =
 (let t := fixture s 3 2147483649 31; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (2147483649 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat), 7) (fixture s 3 2147483649 31) = _
  have numeric : ((BitVec.sshiftRight (2147483649 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_3_2_0
example (s : riscv_state) : «dfn'SRA» (0,1,2) (fixture s 3 4294967297 32) =
 (let t := fixture s 3 4294967297 32; t) := by
  change «write'GPR» ((BitVec.sshiftRight (4294967297 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (32 : BitVec 64))).toNat), 0) (fixture s 3 4294967297 32) = _
  have numeric : ((BitVec.sshiftRight (4294967297 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (32 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_3_2_1
example (s : riscv_state) : «dfn'SRA» (1,1,2) (fixture s 3 4294967297 32) =
 (let t := fixture s 3 4294967297 32; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (4294967297 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (32 : BitVec 64))).toNat), 1) (fixture s 3 4294967297 32) = _
  have numeric : ((BitVec.sshiftRight (4294967297 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (32 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_3_2_2
example (s : riscv_state) : «dfn'SRA» (2,1,2) (fixture s 3 4294967297 32) =
 (let t := fixture s 3 4294967297 32; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (4294967297 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (32 : BitVec 64))).toNat), 2) (fixture s 3 4294967297 32) = _
  have numeric : ((BitVec.sshiftRight (4294967297 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (32 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_3_2_7
example (s : riscv_state) : «dfn'SRA» (7,1,2) (fixture s 3 4294967297 32) =
 (let t := fixture s 3 4294967297 32; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (4294967297 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (32 : BitVec 64))).toNat), 7) (fixture s 3 4294967297 32) = _
  have numeric : ((BitVec.sshiftRight (4294967297 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (32 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_3_3_0
example (s : riscv_state) : «dfn'SRA» (0,1,2) (fixture s 3 18446744073709551615 63) =
 (let t := fixture s 3 18446744073709551615 63; t) := by
  change «write'GPR» ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (63 : BitVec 64))).toNat), 0) (fixture s 3 18446744073709551615 63) = _
  have numeric : ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (63 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_3_3_1
example (s : riscv_state) : «dfn'SRA» (1,1,2) (fixture s 3 18446744073709551615 63) =
 (let t := fixture s 3 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (63 : BitVec 64))).toNat), 1) (fixture s 3 18446744073709551615 63) = _
  have numeric : ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (63 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_3_3_2
example (s : riscv_state) : «dfn'SRA» (2,1,2) (fixture s 3 18446744073709551615 63) =
 (let t := fixture s 3 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (63 : BitVec 64))).toNat), 2) (fixture s 3 18446744073709551615 63) = _
  have numeric : ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (63 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_3_3_7
example (s : riscv_state) : «dfn'SRA» (7,1,2) (fixture s 3 18446744073709551615 63) =
 (let t := fixture s 3 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (63 : BitVec 64))).toNat), 7) (fixture s 3 18446744073709551615 63) = _
  have numeric : ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (63 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_3_4_0
example (s : riscv_state) : «dfn'SRA» (0,1,2) (fixture s 3 2147483648 64) =
 (let t := fixture s 3 2147483648 64; t) := by
  change «write'GPR» ((BitVec.sshiftRight (2147483648 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (64 : BitVec 64))).toNat), 0) (fixture s 3 2147483648 64) = _
  have numeric : ((BitVec.sshiftRight (2147483648 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (64 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_3_4_1
example (s : riscv_state) : «dfn'SRA» (1,1,2) (fixture s 3 2147483648 64) =
 (let t := fixture s 3 2147483648 64; {t with c_gpr := holUpdate 7 (holUpdate 1 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (2147483648 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (64 : BitVec 64))).toNat), 1) (fixture s 3 2147483648 64) = _
  have numeric : ((BitVec.sshiftRight (2147483648 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (64 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_3_4_2
example (s : riscv_state) : «dfn'SRA» (2,1,2) (fixture s 3 2147483648 64) =
 (let t := fixture s 3 2147483648 64; {t with c_gpr := holUpdate 7 (holUpdate 2 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (2147483648 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (64 : BitVec 64))).toNat), 2) (fixture s 3 2147483648 64) = _
  have numeric : ((BitVec.sshiftRight (2147483648 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (64 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_3_4_7
example (s : riscv_state) : «dfn'SRA» (7,1,2) (fixture s 3 2147483648 64) =
 (let t := fixture s 3 2147483648 64; {t with c_gpr := holUpdate 7 (holUpdate 7 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (2147483648 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (64 : BitVec 64))).toNat), 7) (fixture s 3 2147483648 64) = _
  have numeric : ((BitVec.sshiftRight (2147483648 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (64 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_3_5_0
example (s : riscv_state) : «dfn'SRA» (0,1,2) (fixture s 3 4294967296 65) =
 (let t := fixture s 3 4294967296 65; t) := by
  change «write'GPR» ((BitVec.sshiftRight (4294967296 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (65 : BitVec 64))).toNat), 0) (fixture s 3 4294967296 65) = _
  have numeric : ((BitVec.sshiftRight (4294967296 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (65 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_3_5_1
example (s : riscv_state) : «dfn'SRA» (1,1,2) (fixture s 3 4294967296 65) =
 (let t := fixture s 3 4294967296 65; {t with c_gpr := holUpdate 7 (holUpdate 1 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (4294967296 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (65 : BitVec 64))).toNat), 1) (fixture s 3 4294967296 65) = _
  have numeric : ((BitVec.sshiftRight (4294967296 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (65 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_3_5_2
example (s : riscv_state) : «dfn'SRA» (2,1,2) (fixture s 3 4294967296 65) =
 (let t := fixture s 3 4294967296 65; {t with c_gpr := holUpdate 7 (holUpdate 2 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (4294967296 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (65 : BitVec 64))).toNat), 2) (fixture s 3 4294967296 65) = _
  have numeric : ((BitVec.sshiftRight (4294967296 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (65 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_3_5_7
example (s : riscv_state) : «dfn'SRA» (7,1,2) (fixture s 3 4294967296 65) =
 (let t := fixture s 3 4294967296 65; {t with c_gpr := holUpdate 7 (holUpdate 7 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (4294967296 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (65 : BitVec 64))).toNat), 7) (fixture s 3 4294967296 65) = _
  have numeric : ((BitVec.sshiftRight (4294967296 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (65 : BitVec 64))).toNat)) = (2147483648 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_3_6_0
example (s : riscv_state) : «dfn'SRA» (0,1,2) (fixture s 3 9223372036854775809 127) =
 (let t := fixture s 3 9223372036854775809 127; t) := by
  change «write'GPR» ((BitVec.sshiftRight (9223372036854775809 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (127 : BitVec 64))).toNat), 0) (fixture s 3 9223372036854775809 127) = _
  have numeric : ((BitVec.sshiftRight (9223372036854775809 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (127 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_3_6_1
example (s : riscv_state) : «dfn'SRA» (1,1,2) (fixture s 3 9223372036854775809 127) =
 (let t := fixture s 3 9223372036854775809 127; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (9223372036854775809 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (127 : BitVec 64))).toNat), 1) (fixture s 3 9223372036854775809 127) = _
  have numeric : ((BitVec.sshiftRight (9223372036854775809 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (127 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_3_6_2
example (s : riscv_state) : «dfn'SRA» (2,1,2) (fixture s 3 9223372036854775809 127) =
 (let t := fixture s 3 9223372036854775809 127; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (9223372036854775809 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (127 : BitVec 64))).toNat), 2) (fixture s 3 9223372036854775809 127) = _
  have numeric : ((BitVec.sshiftRight (9223372036854775809 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (127 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_3_6_7
example (s : riscv_state) : «dfn'SRA» (7,1,2) (fixture s 3 9223372036854775809 127) =
 (let t := fixture s 3 9223372036854775809 127; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (9223372036854775809 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (127 : BitVec 64))).toNat), 7) (fixture s 3 9223372036854775809 127) = _
  have numeric : ((BitVec.sshiftRight (9223372036854775809 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (127 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_3_7_0
example (s : riscv_state) : «dfn'SRA» (0,1,2) (fixture s 3 17 129) =
 (let t := fixture s 3 17 129; t) := by
  change «write'GPR» ((BitVec.sshiftRight (17 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (129 : BitVec 64))).toNat), 0) (fixture s 3 17 129) = _
  have numeric : ((BitVec.sshiftRight (17 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (129 : BitVec 64))).toNat)) = (8 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_3_7_1
example (s : riscv_state) : «dfn'SRA» (1,1,2) (fixture s 3 17 129) =
 (let t := fixture s 3 17 129; {t with c_gpr := holUpdate 7 (holUpdate 1 8 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (17 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (129 : BitVec 64))).toNat), 1) (fixture s 3 17 129) = _
  have numeric : ((BitVec.sshiftRight (17 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (129 : BitVec 64))).toNat)) = (8 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_3_7_2
example (s : riscv_state) : «dfn'SRA» (2,1,2) (fixture s 3 17 129) =
 (let t := fixture s 3 17 129; {t with c_gpr := holUpdate 7 (holUpdate 2 8 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (17 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (129 : BitVec 64))).toNat), 2) (fixture s 3 17 129) = _
  have numeric : ((BitVec.sshiftRight (17 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (129 : BitVec 64))).toNat)) = (8 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_3_7_7
example (s : riscv_state) : «dfn'SRA» (7,1,2) (fixture s 3 17 129) =
 (let t := fixture s 3 17 129; {t with c_gpr := holUpdate 7 (holUpdate 7 8 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (17 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (129 : BitVec 64))).toNat), 7) (fixture s 3 17 129) = _
  have numeric : ((BitVec.sshiftRight (17 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (129 : BitVec 64))).toNat)) = (8 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_3_8_0
example (s : riscv_state) : «dfn'SRA» (0,0,2) (fixture s 3 17 31) =
 (let t := fixture s 3 17 31; t) := by
  change «write'GPR» ((BitVec.sshiftRight (0 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat), 0) (fixture s 3 17 31) = _
  have numeric : ((BitVec.sshiftRight (0 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_3_8_1
example (s : riscv_state) : «dfn'SRA» (1,0,2) (fixture s 3 17 31) =
 (let t := fixture s 3 17 31; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (0 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat), 1) (fixture s 3 17 31) = _
  have numeric : ((BitVec.sshiftRight (0 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_3_8_2
example (s : riscv_state) : «dfn'SRA» (2,0,2) (fixture s 3 17 31) =
 (let t := fixture s 3 17 31; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (0 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat), 2) (fixture s 3 17 31) = _
  have numeric : ((BitVec.sshiftRight (0 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_3_8_7
example (s : riscv_state) : «dfn'SRA» (7,0,2) (fixture s 3 17 31) =
 (let t := fixture s 3 17 31; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (0 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat), 7) (fixture s 3 17 31) = _
  have numeric : ((BitVec.sshiftRight (0 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_3_9_0
example (s : riscv_state) : «dfn'SRA» (0,1,0) (fixture s 3 18446744073709551615 63) =
 (let t := fixture s 3 18446744073709551615 63; t) := by
  change «write'GPR» ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat), 0) (fixture s 3 18446744073709551615 63) = _
  have numeric : ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_3_9_1
example (s : riscv_state) : «dfn'SRA» (1,1,0) (fixture s 3 18446744073709551615 63) =
 (let t := fixture s 3 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat), 1) (fixture s 3 18446744073709551615 63) = _
  have numeric : ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_3_9_2
example (s : riscv_state) : «dfn'SRA» (2,1,0) (fixture s 3 18446744073709551615 63) =
 (let t := fixture s 3 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat), 2) (fixture s 3 18446744073709551615 63) = _
  have numeric : ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRA_3_9_7
example (s : riscv_state) : «dfn'SRA» (7,1,0) (fixture s 3 18446744073709551615 63) =
 (let t := fixture s 3 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat), 7) (fixture s 3 18446744073709551615 63) = _
  have numeric : ((BitVec.sshiftRight (18446744073709551615 : BitVec 64) (BitVec.setWidth 64 (holWordExtract 6 5 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_0_0_0
example (s : riscv_state) : «dfn'SRAW» (0,1,2) (fixture s 0 9223372036854775808 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775808 0) := by rfl

-- register_shift_SRAW_0_0_1
example (s : riscv_state) : «dfn'SRAW» (1,1,2) (fixture s 0 9223372036854775808 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775808 0) := by rfl

-- register_shift_SRAW_0_0_2
example (s : riscv_state) : «dfn'SRAW» (2,1,2) (fixture s 0 9223372036854775808 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775808 0) := by rfl

-- register_shift_SRAW_0_0_7
example (s : riscv_state) : «dfn'SRAW» (7,1,2) (fixture s 0 9223372036854775808 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775808 0) := by rfl

-- register_shift_SRAW_0_1_0
example (s : riscv_state) : «dfn'SRAW» (0,1,2) (fixture s 0 2147483649 31) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483649 31) := by rfl

-- register_shift_SRAW_0_1_1
example (s : riscv_state) : «dfn'SRAW» (1,1,2) (fixture s 0 2147483649 31) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483649 31) := by rfl

-- register_shift_SRAW_0_1_2
example (s : riscv_state) : «dfn'SRAW» (2,1,2) (fixture s 0 2147483649 31) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483649 31) := by rfl

-- register_shift_SRAW_0_1_7
example (s : riscv_state) : «dfn'SRAW» (7,1,2) (fixture s 0 2147483649 31) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483649 31) := by rfl

-- register_shift_SRAW_0_2_0
example (s : riscv_state) : «dfn'SRAW» (0,1,2) (fixture s 0 4294967297 32) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967297 32) := by rfl

-- register_shift_SRAW_0_2_1
example (s : riscv_state) : «dfn'SRAW» (1,1,2) (fixture s 0 4294967297 32) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967297 32) := by rfl

-- register_shift_SRAW_0_2_2
example (s : riscv_state) : «dfn'SRAW» (2,1,2) (fixture s 0 4294967297 32) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967297 32) := by rfl

-- register_shift_SRAW_0_2_7
example (s : riscv_state) : «dfn'SRAW» (7,1,2) (fixture s 0 4294967297 32) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967297 32) := by rfl

-- register_shift_SRAW_0_3_0
example (s : riscv_state) : «dfn'SRAW» (0,1,2) (fixture s 0 18446744073709551615 63) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 63) := by rfl

-- register_shift_SRAW_0_3_1
example (s : riscv_state) : «dfn'SRAW» (1,1,2) (fixture s 0 18446744073709551615 63) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 63) := by rfl

-- register_shift_SRAW_0_3_2
example (s : riscv_state) : «dfn'SRAW» (2,1,2) (fixture s 0 18446744073709551615 63) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 63) := by rfl

-- register_shift_SRAW_0_3_7
example (s : riscv_state) : «dfn'SRAW» (7,1,2) (fixture s 0 18446744073709551615 63) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 63) := by rfl

-- register_shift_SRAW_0_4_0
example (s : riscv_state) : «dfn'SRAW» (0,1,2) (fixture s 0 2147483648 64) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483648 64) := by rfl

-- register_shift_SRAW_0_4_1
example (s : riscv_state) : «dfn'SRAW» (1,1,2) (fixture s 0 2147483648 64) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483648 64) := by rfl

-- register_shift_SRAW_0_4_2
example (s : riscv_state) : «dfn'SRAW» (2,1,2) (fixture s 0 2147483648 64) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483648 64) := by rfl

-- register_shift_SRAW_0_4_7
example (s : riscv_state) : «dfn'SRAW» (7,1,2) (fixture s 0 2147483648 64) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483648 64) := by rfl

-- register_shift_SRAW_0_5_0
example (s : riscv_state) : «dfn'SRAW» (0,1,2) (fixture s 0 4294967296 65) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967296 65) := by rfl

-- register_shift_SRAW_0_5_1
example (s : riscv_state) : «dfn'SRAW» (1,1,2) (fixture s 0 4294967296 65) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967296 65) := by rfl

-- register_shift_SRAW_0_5_2
example (s : riscv_state) : «dfn'SRAW» (2,1,2) (fixture s 0 4294967296 65) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967296 65) := by rfl

-- register_shift_SRAW_0_5_7
example (s : riscv_state) : «dfn'SRAW» (7,1,2) (fixture s 0 4294967296 65) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967296 65) := by rfl

-- register_shift_SRAW_0_6_0
example (s : riscv_state) : «dfn'SRAW» (0,1,2) (fixture s 0 9223372036854775809 127) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775809 127) := by rfl

-- register_shift_SRAW_0_6_1
example (s : riscv_state) : «dfn'SRAW» (1,1,2) (fixture s 0 9223372036854775809 127) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775809 127) := by rfl

-- register_shift_SRAW_0_6_2
example (s : riscv_state) : «dfn'SRAW» (2,1,2) (fixture s 0 9223372036854775809 127) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775809 127) := by rfl

-- register_shift_SRAW_0_6_7
example (s : riscv_state) : «dfn'SRAW» (7,1,2) (fixture s 0 9223372036854775809 127) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775809 127) := by rfl

-- register_shift_SRAW_0_7_0
example (s : riscv_state) : «dfn'SRAW» (0,1,2) (fixture s 0 17 129) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 129) := by rfl

-- register_shift_SRAW_0_7_1
example (s : riscv_state) : «dfn'SRAW» (1,1,2) (fixture s 0 17 129) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 129) := by rfl

-- register_shift_SRAW_0_7_2
example (s : riscv_state) : «dfn'SRAW» (2,1,2) (fixture s 0 17 129) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 129) := by rfl

-- register_shift_SRAW_0_7_7
example (s : riscv_state) : «dfn'SRAW» (7,1,2) (fixture s 0 17 129) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 129) := by rfl

-- register_shift_SRAW_0_8_0
example (s : riscv_state) : «dfn'SRAW» (0,0,2) (fixture s 0 17 31) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 31) := by rfl

-- register_shift_SRAW_0_8_1
example (s : riscv_state) : «dfn'SRAW» (1,0,2) (fixture s 0 17 31) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 31) := by rfl

-- register_shift_SRAW_0_8_2
example (s : riscv_state) : «dfn'SRAW» (2,0,2) (fixture s 0 17 31) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 31) := by rfl

-- register_shift_SRAW_0_8_7
example (s : riscv_state) : «dfn'SRAW» (7,0,2) (fixture s 0 17 31) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 31) := by rfl

-- register_shift_SRAW_0_9_0
example (s : riscv_state) : «dfn'SRAW» (0,1,0) (fixture s 0 18446744073709551615 63) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 63) := by rfl

-- register_shift_SRAW_0_9_1
example (s : riscv_state) : «dfn'SRAW» (1,1,0) (fixture s 0 18446744073709551615 63) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 63) := by rfl

-- register_shift_SRAW_0_9_2
example (s : riscv_state) : «dfn'SRAW» (2,1,0) (fixture s 0 18446744073709551615 63) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 63) := by rfl

-- register_shift_SRAW_0_9_7
example (s : riscv_state) : «dfn'SRAW» (7,1,0) (fixture s 0 18446744073709551615 63) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 63) := by rfl

-- register_shift_SRAW_2_0_0
example (s : riscv_state) : «dfn'SRAW» (0,1,2) (fixture s 2 9223372036854775808 0) =
 (let t := fixture s 2 9223372036854775808 0; t) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 0) (fixture s 2 9223372036854775808 0) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_2_0_1
example (s : riscv_state) : «dfn'SRAW» (1,1,2) (fixture s 2 9223372036854775808 0) =
 (let t := fixture s 2 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 1) (fixture s 2 9223372036854775808 0) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_2_0_2
example (s : riscv_state) : «dfn'SRAW» (2,1,2) (fixture s 2 9223372036854775808 0) =
 (let t := fixture s 2 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 2) (fixture s 2 9223372036854775808 0) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_2_0_7
example (s : riscv_state) : «dfn'SRAW» (7,1,2) (fixture s 2 9223372036854775808 0) =
 (let t := fixture s 2 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 7) (fixture s 2 9223372036854775808 0) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_2_1_0
example (s : riscv_state) : «dfn'SRAW» (0,1,2) (fixture s 2 2147483649 31) =
 (let t := fixture s 2 2147483649 31; t) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (2147483649 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 0) (fixture s 2 2147483649 31) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (2147483649 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_2_1_1
example (s : riscv_state) : «dfn'SRAW» (1,1,2) (fixture s 2 2147483649 31) =
 (let t := fixture s 2 2147483649 31; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (2147483649 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 1) (fixture s 2 2147483649 31) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (2147483649 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_2_1_2
example (s : riscv_state) : «dfn'SRAW» (2,1,2) (fixture s 2 2147483649 31) =
 (let t := fixture s 2 2147483649 31; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (2147483649 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 2) (fixture s 2 2147483649 31) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (2147483649 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_2_1_7
example (s : riscv_state) : «dfn'SRAW» (7,1,2) (fixture s 2 2147483649 31) =
 (let t := fixture s 2 2147483649 31; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (2147483649 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 7) (fixture s 2 2147483649 31) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (2147483649 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_2_2_0
example (s : riscv_state) : «dfn'SRAW» (0,1,2) (fixture s 2 4294967297 32) =
 (let t := fixture s 2 4294967297 32; t) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (4294967297 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat), 0) (fixture s 2 4294967297 32) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (4294967297 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_2_2_1
example (s : riscv_state) : «dfn'SRAW» (1,1,2) (fixture s 2 4294967297 32) =
 (let t := fixture s 2 4294967297 32; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (4294967297 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat), 1) (fixture s 2 4294967297 32) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (4294967297 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_2_2_2
example (s : riscv_state) : «dfn'SRAW» (2,1,2) (fixture s 2 4294967297 32) =
 (let t := fixture s 2 4294967297 32; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (4294967297 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat), 2) (fixture s 2 4294967297 32) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (4294967297 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_2_2_7
example (s : riscv_state) : «dfn'SRAW» (7,1,2) (fixture s 2 4294967297 32) =
 (let t := fixture s 2 4294967297 32; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (4294967297 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat), 7) (fixture s 2 4294967297 32) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (4294967297 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_2_3_0
example (s : riscv_state) : «dfn'SRAW» (0,1,2) (fixture s 2 18446744073709551615 63) =
 (let t := fixture s 2 18446744073709551615 63; t) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat), 0) (fixture s 2 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_2_3_1
example (s : riscv_state) : «dfn'SRAW» (1,1,2) (fixture s 2 18446744073709551615 63) =
 (let t := fixture s 2 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat), 1) (fixture s 2 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_2_3_2
example (s : riscv_state) : «dfn'SRAW» (2,1,2) (fixture s 2 18446744073709551615 63) =
 (let t := fixture s 2 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat), 2) (fixture s 2 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_2_3_7
example (s : riscv_state) : «dfn'SRAW» (7,1,2) (fixture s 2 18446744073709551615 63) =
 (let t := fixture s 2 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat), 7) (fixture s 2 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_2_4_0
example (s : riscv_state) : «dfn'SRAW» (0,1,2) (fixture s 2 2147483648 64) =
 (let t := fixture s 2 2147483648 64; t) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (2147483648 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat), 0) (fixture s 2 2147483648 64) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (2147483648 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_2_4_1
example (s : riscv_state) : «dfn'SRAW» (1,1,2) (fixture s 2 2147483648 64) =
 (let t := fixture s 2 2147483648 64; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (2147483648 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat), 1) (fixture s 2 2147483648 64) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (2147483648 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_2_4_2
example (s : riscv_state) : «dfn'SRAW» (2,1,2) (fixture s 2 2147483648 64) =
 (let t := fixture s 2 2147483648 64; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (2147483648 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat), 2) (fixture s 2 2147483648 64) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (2147483648 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_2_4_7
example (s : riscv_state) : «dfn'SRAW» (7,1,2) (fixture s 2 2147483648 64) =
 (let t := fixture s 2 2147483648 64; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (2147483648 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat), 7) (fixture s 2 2147483648 64) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (2147483648 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_2_5_0
example (s : riscv_state) : «dfn'SRAW» (0,1,2) (fixture s 2 4294967296 65) =
 (let t := fixture s 2 4294967296 65; t) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (4294967296 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat), 0) (fixture s 2 4294967296 65) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (4294967296 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_2_5_1
example (s : riscv_state) : «dfn'SRAW» (1,1,2) (fixture s 2 4294967296 65) =
 (let t := fixture s 2 4294967296 65; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (4294967296 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat), 1) (fixture s 2 4294967296 65) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (4294967296 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_2_5_2
example (s : riscv_state) : «dfn'SRAW» (2,1,2) (fixture s 2 4294967296 65) =
 (let t := fixture s 2 4294967296 65; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (4294967296 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat), 2) (fixture s 2 4294967296 65) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (4294967296 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_2_5_7
example (s : riscv_state) : «dfn'SRAW» (7,1,2) (fixture s 2 4294967296 65) =
 (let t := fixture s 2 4294967296 65; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (4294967296 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat), 7) (fixture s 2 4294967296 65) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (4294967296 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_2_6_0
example (s : riscv_state) : «dfn'SRAW» (0,1,2) (fixture s 2 9223372036854775809 127) =
 (let t := fixture s 2 9223372036854775809 127; t) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat), 0) (fixture s 2 9223372036854775809 127) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_2_6_1
example (s : riscv_state) : «dfn'SRAW» (1,1,2) (fixture s 2 9223372036854775809 127) =
 (let t := fixture s 2 9223372036854775809 127; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat), 1) (fixture s 2 9223372036854775809 127) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_2_6_2
example (s : riscv_state) : «dfn'SRAW» (2,1,2) (fixture s 2 9223372036854775809 127) =
 (let t := fixture s 2 9223372036854775809 127; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat), 2) (fixture s 2 9223372036854775809 127) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_2_6_7
example (s : riscv_state) : «dfn'SRAW» (7,1,2) (fixture s 2 9223372036854775809 127) =
 (let t := fixture s 2 9223372036854775809 127; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat), 7) (fixture s 2 9223372036854775809 127) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_2_7_0
example (s : riscv_state) : «dfn'SRAW» (0,1,2) (fixture s 2 17 129) =
 (let t := fixture s 2 17 129; t) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (17 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat), 0) (fixture s 2 17 129) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (17 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat)) = (8 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_2_7_1
example (s : riscv_state) : «dfn'SRAW» (1,1,2) (fixture s 2 17 129) =
 (let t := fixture s 2 17 129; {t with c_gpr := holUpdate 7 (holUpdate 1 8 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (17 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat), 1) (fixture s 2 17 129) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (17 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat)) = (8 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_2_7_2
example (s : riscv_state) : «dfn'SRAW» (2,1,2) (fixture s 2 17 129) =
 (let t := fixture s 2 17 129; {t with c_gpr := holUpdate 7 (holUpdate 2 8 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (17 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat), 2) (fixture s 2 17 129) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (17 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat)) = (8 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_2_7_7
example (s : riscv_state) : «dfn'SRAW» (7,1,2) (fixture s 2 17 129) =
 (let t := fixture s 2 17 129; {t with c_gpr := holUpdate 7 (holUpdate 7 8 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (17 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat), 7) (fixture s 2 17 129) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (17 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat)) = (8 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_2_8_0
example (s : riscv_state) : «dfn'SRAW» (0,0,2) (fixture s 2 17 31) =
 (let t := fixture s 2 17 31; t) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (0 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 0) (fixture s 2 17 31) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (0 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_2_8_1
example (s : riscv_state) : «dfn'SRAW» (1,0,2) (fixture s 2 17 31) =
 (let t := fixture s 2 17 31; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (0 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 1) (fixture s 2 17 31) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (0 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_2_8_2
example (s : riscv_state) : «dfn'SRAW» (2,0,2) (fixture s 2 17 31) =
 (let t := fixture s 2 17 31; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (0 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 2) (fixture s 2 17 31) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (0 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_2_8_7
example (s : riscv_state) : «dfn'SRAW» (7,0,2) (fixture s 2 17 31) =
 (let t := fixture s 2 17 31; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (0 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 7) (fixture s 2 17 31) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (0 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_2_9_0
example (s : riscv_state) : «dfn'SRAW» (0,1,0) (fixture s 2 18446744073709551615 63) =
 (let t := fixture s 2 18446744073709551615 63; t) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 0) (fixture s 2 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_2_9_1
example (s : riscv_state) : «dfn'SRAW» (1,1,0) (fixture s 2 18446744073709551615 63) =
 (let t := fixture s 2 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 1) (fixture s 2 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_2_9_2
example (s : riscv_state) : «dfn'SRAW» (2,1,0) (fixture s 2 18446744073709551615 63) =
 (let t := fixture s 2 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 2) (fixture s 2 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_2_9_7
example (s : riscv_state) : «dfn'SRAW» (7,1,0) (fixture s 2 18446744073709551615 63) =
 (let t := fixture s 2 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 7) (fixture s 2 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_3_0_0
example (s : riscv_state) : «dfn'SRAW» (0,1,2) (fixture s 3 9223372036854775808 0) =
 (let t := fixture s 3 9223372036854775808 0; t) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 0) (fixture s 3 9223372036854775808 0) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_3_0_1
example (s : riscv_state) : «dfn'SRAW» (1,1,2) (fixture s 3 9223372036854775808 0) =
 (let t := fixture s 3 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 1) (fixture s 3 9223372036854775808 0) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_3_0_2
example (s : riscv_state) : «dfn'SRAW» (2,1,2) (fixture s 3 9223372036854775808 0) =
 (let t := fixture s 3 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 2) (fixture s 3 9223372036854775808 0) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_3_0_7
example (s : riscv_state) : «dfn'SRAW» (7,1,2) (fixture s 3 9223372036854775808 0) =
 (let t := fixture s 3 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 7) (fixture s 3 9223372036854775808 0) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_3_1_0
example (s : riscv_state) : «dfn'SRAW» (0,1,2) (fixture s 3 2147483649 31) =
 (let t := fixture s 3 2147483649 31; t) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (2147483649 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 0) (fixture s 3 2147483649 31) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (2147483649 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_3_1_1
example (s : riscv_state) : «dfn'SRAW» (1,1,2) (fixture s 3 2147483649 31) =
 (let t := fixture s 3 2147483649 31; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (2147483649 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 1) (fixture s 3 2147483649 31) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (2147483649 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_3_1_2
example (s : riscv_state) : «dfn'SRAW» (2,1,2) (fixture s 3 2147483649 31) =
 (let t := fixture s 3 2147483649 31; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (2147483649 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 2) (fixture s 3 2147483649 31) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (2147483649 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_3_1_7
example (s : riscv_state) : «dfn'SRAW» (7,1,2) (fixture s 3 2147483649 31) =
 (let t := fixture s 3 2147483649 31; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (2147483649 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 7) (fixture s 3 2147483649 31) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (2147483649 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_3_2_0
example (s : riscv_state) : «dfn'SRAW» (0,1,2) (fixture s 3 4294967297 32) =
 (let t := fixture s 3 4294967297 32; t) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (4294967297 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat), 0) (fixture s 3 4294967297 32) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (4294967297 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_3_2_1
example (s : riscv_state) : «dfn'SRAW» (1,1,2) (fixture s 3 4294967297 32) =
 (let t := fixture s 3 4294967297 32; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (4294967297 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat), 1) (fixture s 3 4294967297 32) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (4294967297 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_3_2_2
example (s : riscv_state) : «dfn'SRAW» (2,1,2) (fixture s 3 4294967297 32) =
 (let t := fixture s 3 4294967297 32; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (4294967297 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat), 2) (fixture s 3 4294967297 32) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (4294967297 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_3_2_7
example (s : riscv_state) : «dfn'SRAW» (7,1,2) (fixture s 3 4294967297 32) =
 (let t := fixture s 3 4294967297 32; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (4294967297 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat), 7) (fixture s 3 4294967297 32) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (4294967297 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (32 : BitVec 64))).toNat)) = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_3_3_0
example (s : riscv_state) : «dfn'SRAW» (0,1,2) (fixture s 3 18446744073709551615 63) =
 (let t := fixture s 3 18446744073709551615 63; t) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat), 0) (fixture s 3 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_3_3_1
example (s : riscv_state) : «dfn'SRAW» (1,1,2) (fixture s 3 18446744073709551615 63) =
 (let t := fixture s 3 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat), 1) (fixture s 3 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_3_3_2
example (s : riscv_state) : «dfn'SRAW» (2,1,2) (fixture s 3 18446744073709551615 63) =
 (let t := fixture s 3 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat), 2) (fixture s 3 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_3_3_7
example (s : riscv_state) : «dfn'SRAW» (7,1,2) (fixture s 3 18446744073709551615 63) =
 (let t := fixture s 3 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat), 7) (fixture s 3 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (63 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_3_4_0
example (s : riscv_state) : «dfn'SRAW» (0,1,2) (fixture s 3 2147483648 64) =
 (let t := fixture s 3 2147483648 64; t) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (2147483648 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat), 0) (fixture s 3 2147483648 64) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (2147483648 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_3_4_1
example (s : riscv_state) : «dfn'SRAW» (1,1,2) (fixture s 3 2147483648 64) =
 (let t := fixture s 3 2147483648 64; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (2147483648 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat), 1) (fixture s 3 2147483648 64) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (2147483648 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_3_4_2
example (s : riscv_state) : «dfn'SRAW» (2,1,2) (fixture s 3 2147483648 64) =
 (let t := fixture s 3 2147483648 64; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (2147483648 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat), 2) (fixture s 3 2147483648 64) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (2147483648 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_3_4_7
example (s : riscv_state) : «dfn'SRAW» (7,1,2) (fixture s 3 2147483648 64) =
 (let t := fixture s 3 2147483648 64; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (2147483648 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat), 7) (fixture s 3 2147483648 64) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (2147483648 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (64 : BitVec 64))).toNat)) = (18446744071562067968 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_3_5_0
example (s : riscv_state) : «dfn'SRAW» (0,1,2) (fixture s 3 4294967296 65) =
 (let t := fixture s 3 4294967296 65; t) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (4294967296 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat), 0) (fixture s 3 4294967296 65) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (4294967296 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_3_5_1
example (s : riscv_state) : «dfn'SRAW» (1,1,2) (fixture s 3 4294967296 65) =
 (let t := fixture s 3 4294967296 65; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (4294967296 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat), 1) (fixture s 3 4294967296 65) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (4294967296 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_3_5_2
example (s : riscv_state) : «dfn'SRAW» (2,1,2) (fixture s 3 4294967296 65) =
 (let t := fixture s 3 4294967296 65; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (4294967296 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat), 2) (fixture s 3 4294967296 65) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (4294967296 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_3_5_7
example (s : riscv_state) : «dfn'SRAW» (7,1,2) (fixture s 3 4294967296 65) =
 (let t := fixture s 3 4294967296 65; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (4294967296 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat), 7) (fixture s 3 4294967296 65) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (4294967296 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (65 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_3_6_0
example (s : riscv_state) : «dfn'SRAW» (0,1,2) (fixture s 3 9223372036854775809 127) =
 (let t := fixture s 3 9223372036854775809 127; t) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat), 0) (fixture s 3 9223372036854775809 127) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_3_6_1
example (s : riscv_state) : «dfn'SRAW» (1,1,2) (fixture s 3 9223372036854775809 127) =
 (let t := fixture s 3 9223372036854775809 127; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat), 1) (fixture s 3 9223372036854775809 127) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_3_6_2
example (s : riscv_state) : «dfn'SRAW» (2,1,2) (fixture s 3 9223372036854775809 127) =
 (let t := fixture s 3 9223372036854775809 127; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat), 2) (fixture s 3 9223372036854775809 127) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_3_6_7
example (s : riscv_state) : «dfn'SRAW» (7,1,2) (fixture s 3 9223372036854775809 127) =
 (let t := fixture s 3 9223372036854775809 127; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat), 7) (fixture s 3 9223372036854775809 127) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (9223372036854775809 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (127 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_3_7_0
example (s : riscv_state) : «dfn'SRAW» (0,1,2) (fixture s 3 17 129) =
 (let t := fixture s 3 17 129; t) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (17 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat), 0) (fixture s 3 17 129) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (17 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat)) = (8 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_3_7_1
example (s : riscv_state) : «dfn'SRAW» (1,1,2) (fixture s 3 17 129) =
 (let t := fixture s 3 17 129; {t with c_gpr := holUpdate 7 (holUpdate 1 8 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (17 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat), 1) (fixture s 3 17 129) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (17 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat)) = (8 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_3_7_2
example (s : riscv_state) : «dfn'SRAW» (2,1,2) (fixture s 3 17 129) =
 (let t := fixture s 3 17 129; {t with c_gpr := holUpdate 7 (holUpdate 2 8 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (17 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat), 2) (fixture s 3 17 129) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (17 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat)) = (8 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_3_7_7
example (s : riscv_state) : «dfn'SRAW» (7,1,2) (fixture s 3 17 129) =
 (let t := fixture s 3 17 129; {t with c_gpr := holUpdate 7 (holUpdate 7 8 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (17 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat), 7) (fixture s 3 17 129) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (17 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (129 : BitVec 64))).toNat)) = (8 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_3_8_0
example (s : riscv_state) : «dfn'SRAW» (0,0,2) (fixture s 3 17 31) =
 (let t := fixture s 3 17 31; t) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (0 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 0) (fixture s 3 17 31) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (0 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_3_8_1
example (s : riscv_state) : «dfn'SRAW» (1,0,2) (fixture s 3 17 31) =
 (let t := fixture s 3 17 31; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (0 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 1) (fixture s 3 17 31) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (0 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_3_8_2
example (s : riscv_state) : «dfn'SRAW» (2,0,2) (fixture s 3 17 31) =
 (let t := fixture s 3 17 31; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (0 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 2) (fixture s 3 17 31) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (0 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_3_8_7
example (s : riscv_state) : «dfn'SRAW» (7,0,2) (fixture s 3 17 31) =
 (let t := fixture s 3 17 31; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (0 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat), 7) (fixture s 3 17 31) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (0 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (31 : BitVec 64))).toNat)) = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_3_9_0
example (s : riscv_state) : «dfn'SRAW» (0,1,0) (fixture s 3 18446744073709551615 63) =
 (let t := fixture s 3 18446744073709551615 63; t) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 0) (fixture s 3 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_3_9_1
example (s : riscv_state) : «dfn'SRAW» (1,1,0) (fixture s 3 18446744073709551615 63) =
 (let t := fixture s 3 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 1) (fixture s 3 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_3_9_2
example (s : riscv_state) : «dfn'SRAW» (2,1,0) (fixture s 3 18446744073709551615 63) =
 (let t := fixture s 3 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 2) (fixture s 3 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_SRAW_3_9_7
example (s : riscv_state) : «dfn'SRAW» (7,1,0) (fixture s 3 18446744073709551615 63) =
 (let t := fixture s 3 18446744073709551615 63; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat), 7) (fixture s 3 18446744073709551615 63) = _
  have numeric : (BitVec.signExtend 64 (BitVec.sshiftRight (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)) (BitVec.setWidth 32 (holWordExtract 5 4 0 (0 : BitVec 64))).toNat)) = (18446744073709551615 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- register_shift_symbolic_SLLW
example (s : riscv_state) : «dfn'SLLW» (0,0,0) (fixture s 1 17 19) =
 (match in32BitMode () (fixture s 1 17 19) with | (v,u) => if v then signalException ExceptionType.Illegal_Instr u else u) := by
  rfl

-- register_shift_symbolic_SRLW
example (s : riscv_state) : «dfn'SRLW» (0,0,0) (fixture s 1 17 19) =
 (match in32BitMode () (fixture s 1 17 19) with | (v,u) => if v then signalException ExceptionType.Illegal_Instr u else u) := by
  rfl

-- register_shift_symbolic_SRAW
example (s : riscv_state) : «dfn'SRAW» (0,0,0) (fixture s 1 17 19) =
 (match in32BitMode () (fixture s 1 17 19) with | (v,u) => if v then signalException ExceptionType.Illegal_Instr u else u) := by
  rfl


private def unknownMessage : List (BitVec 8) :=
 [85,110,107,110,111,119,110,32,97,114,99,104,105,116,101,99,116,117,114,101,58,32,49]

-- register_shift_invalid_SLL_0_0
example (s : riscv_state) : «dfn'SLL» (0,0,0) ({fixture s 1 17 19 with exception := exception.NoException}) =
 (let t := {fixture s 1 17 19 with exception := exception.NoException}; let u := {t with exception := exception.UNDEFINED unknownMessage}; u) := by
  simp [«dfn'SLL», fixture, in32BitMode, curArch, architecture, MCSR, raiseException_eq, unknownMessage, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, «write'GPR»]
  all_goals (intro _; rfl)

-- register_shift_invalid_SLL_0_1
example (s : riscv_state) : «dfn'SLL» (1,0,0) ({fixture s 1 17 19 with exception := exception.NoException}) =
 (let t := {fixture s 1 17 19 with exception := exception.NoException}; let u := {t with exception := exception.UNDEFINED unknownMessage}; {u with c_gpr := holUpdate 7 (holUpdate 1 0 (u.c_gpr 7)) u.c_gpr}) := by
  simp [«dfn'SLL», fixture, in32BitMode, curArch, architecture, MCSR, GPR, raiseException_eq, unknownMessage, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, «write'GPR», «write'gpr»]
  all_goals (intro _; rfl)

-- register_shift_invalid_SLL_1_0
example (s : riscv_state) : «dfn'SLL» (0,0,0) ({fixture s 1 17 19 with exception := exception.UNDEFINED [9]}) =
 (let t := {fixture s 1 17 19 with exception := exception.UNDEFINED [9]}; let u := {t with exception := exception.UNDEFINED [9]}; u) := by
  simp [«dfn'SLL», fixture, in32BitMode, curArch, architecture, MCSR, raiseException_eq, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, «write'GPR»]
  all_goals (intro _; rfl)

-- register_shift_invalid_SLL_1_1
example (s : riscv_state) : «dfn'SLL» (1,0,0) ({fixture s 1 17 19 with exception := exception.UNDEFINED [9]}) =
 (let t := {fixture s 1 17 19 with exception := exception.UNDEFINED [9]}; let u := {t with exception := exception.UNDEFINED [9]}; {u with c_gpr := holUpdate 7 (holUpdate 1 0 (u.c_gpr 7)) u.c_gpr}) := by
  simp [«dfn'SLL», fixture, in32BitMode, curArch, architecture, MCSR, GPR, raiseException_eq, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, «write'GPR», «write'gpr»]
  all_goals (intro _; rfl)

-- register_shift_invalid_SRL_0_0
example (s : riscv_state) : «dfn'SRL» (0,0,0) ({fixture s 1 17 19 with exception := exception.NoException}) =
 (let t := {fixture s 1 17 19 with exception := exception.NoException}; let u := {t with exception := exception.UNDEFINED unknownMessage}; u) := by
  simp [«dfn'SRL», fixture, in32BitMode, curArch, architecture, MCSR, raiseException_eq, unknownMessage, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, «write'GPR»]
  all_goals (intro _; rfl)

-- register_shift_invalid_SRL_0_1
example (s : riscv_state) : «dfn'SRL» (1,0,0) ({fixture s 1 17 19 with exception := exception.NoException}) =
 (let t := {fixture s 1 17 19 with exception := exception.NoException}; let u := {t with exception := exception.UNDEFINED unknownMessage}; {u with c_gpr := holUpdate 7 (holUpdate 1 0 (u.c_gpr 7)) u.c_gpr}) := by
  simp [«dfn'SRL», fixture, in32BitMode, curArch, architecture, MCSR, GPR, raiseException_eq, unknownMessage, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, «write'GPR», «write'gpr»]
  all_goals (intro _; rfl)

-- register_shift_invalid_SRL_1_0
example (s : riscv_state) : «dfn'SRL» (0,0,0) ({fixture s 1 17 19 with exception := exception.UNDEFINED [9]}) =
 (let t := {fixture s 1 17 19 with exception := exception.UNDEFINED [9]}; let u := {t with exception := exception.UNDEFINED [9]}; u) := by
  simp [«dfn'SRL», fixture, in32BitMode, curArch, architecture, MCSR, raiseException_eq, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, «write'GPR»]
  all_goals (intro _; rfl)

-- register_shift_invalid_SRL_1_1
example (s : riscv_state) : «dfn'SRL» (1,0,0) ({fixture s 1 17 19 with exception := exception.UNDEFINED [9]}) =
 (let t := {fixture s 1 17 19 with exception := exception.UNDEFINED [9]}; let u := {t with exception := exception.UNDEFINED [9]}; {u with c_gpr := holUpdate 7 (holUpdate 1 0 (u.c_gpr 7)) u.c_gpr}) := by
  simp [«dfn'SRL», fixture, in32BitMode, curArch, architecture, MCSR, GPR, raiseException_eq, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, «write'GPR», «write'gpr»]
  all_goals (intro _; rfl)

-- register_shift_invalid_SRA_0_0
example (s : riscv_state) : «dfn'SRA» (0,0,0) ({fixture s 1 17 19 with exception := exception.NoException}) =
 (let t := {fixture s 1 17 19 with exception := exception.NoException}; let u := {t with exception := exception.UNDEFINED unknownMessage}; u) := by
  simp [«dfn'SRA», fixture, in32BitMode, curArch, architecture, MCSR, raiseException_eq, unknownMessage, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, «write'GPR»]
  all_goals (intro _; rfl)

-- register_shift_invalid_SRA_0_1
example (s : riscv_state) : «dfn'SRA» (1,0,0) ({fixture s 1 17 19 with exception := exception.NoException}) =
 (let t := {fixture s 1 17 19 with exception := exception.NoException}; let u := {t with exception := exception.UNDEFINED unknownMessage}; {u with c_gpr := holUpdate 7 (holUpdate 1 0 (u.c_gpr 7)) u.c_gpr}) := by
  simp [«dfn'SRA», fixture, in32BitMode, curArch, architecture, MCSR, GPR, raiseException_eq, unknownMessage, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, «write'GPR», «write'gpr»]
  all_goals (intro _; rfl)

-- register_shift_invalid_SRA_1_0
example (s : riscv_state) : «dfn'SRA» (0,0,0) ({fixture s 1 17 19 with exception := exception.UNDEFINED [9]}) =
 (let t := {fixture s 1 17 19 with exception := exception.UNDEFINED [9]}; let u := {t with exception := exception.UNDEFINED [9]}; u) := by
  simp [«dfn'SRA», fixture, in32BitMode, curArch, architecture, MCSR, raiseException_eq, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, «write'GPR»]
  all_goals (intro _; rfl)

-- register_shift_invalid_SRA_1_1
example (s : riscv_state) : «dfn'SRA» (1,0,0) ({fixture s 1 17 19 with exception := exception.UNDEFINED [9]}) =
 (let t := {fixture s 1 17 19 with exception := exception.UNDEFINED [9]}; let u := {t with exception := exception.UNDEFINED [9]}; {u with c_gpr := holUpdate 7 (holUpdate 1 0 (u.c_gpr 7)) u.c_gpr}) := by
  simp [«dfn'SRA», fixture, in32BitMode, curArch, architecture, MCSR, GPR, raiseException_eq, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, «write'GPR», «write'gpr»]
  all_goals (intro _; rfl)

end Flapjack.Test.L3RegisterShiftParity
