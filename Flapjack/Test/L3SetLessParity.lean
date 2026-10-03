import Flapjack.RiscV.L3.Defs.SetLess

set_option maxRecDepth 20000
namespace Flapjack.Test.L3SetLessParity
open Flapjack.RiscV.L3
private def fixture (s : riscv_state) (mode : BitVec 2) (lhs rhs : BitVec 64) : riscv_state :=
 {s with procID := 7, c_MCSR := fun id => {s.c_MCSR id with mcpuid := {(s.c_MCSR id).mcpuid with ArchBase := mode}}, c_gpr := fun id r => if r = 1 then lhs else if r = 2 then rhs else s.c_gpr id r}

-- set_less_SLT_0_0_0
example (s : riscv_state) : «dfn'SLT» (0,1,2) (fixture s 0 5 7) =
 (let t := fixture s 0 5 7; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (7 : BitVec 64)))], 0) (fixture s 0 5 7) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (7 : BitVec 64)))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_0_0_1
example (s : riscv_state) : «dfn'SLT» (1,1,2) (fixture s 0 5 7) =
 (let t := fixture s 0 5 7; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (7 : BitVec 64)))], 1) (fixture s 0 5 7) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (7 : BitVec 64)))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_0_0_2
example (s : riscv_state) : «dfn'SLT» (2,1,2) (fixture s 0 5 7) =
 (let t := fixture s 0 5 7; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (7 : BitVec 64)))], 2) (fixture s 0 5 7) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (7 : BitVec 64)))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_0_0_7
example (s : riscv_state) : «dfn'SLT» (7,1,2) (fixture s 0 5 7) =
 (let t := fixture s 0 5 7; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (7 : BitVec 64)))], 7) (fixture s 0 5 7) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (7 : BitVec 64)))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_0_1_0
example (s : riscv_state) : «dfn'SLT» (0,1,2) (fixture s 0 7 5) =
 (let t := fixture s 0 7 5; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (7 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64)))], 0) (fixture s 0 7 5) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (7 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_0_1_1
example (s : riscv_state) : «dfn'SLT» (1,1,2) (fixture s 0 7 5) =
 (let t := fixture s 0 7 5; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (7 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64)))], 1) (fixture s 0 7 5) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (7 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_0_1_2
example (s : riscv_state) : «dfn'SLT» (2,1,2) (fixture s 0 7 5) =
 (let t := fixture s 0 7 5; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (7 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64)))], 2) (fixture s 0 7 5) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (7 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_0_1_7
example (s : riscv_state) : «dfn'SLT» (7,1,2) (fixture s 0 7 5) =
 (let t := fixture s 0 7 5; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (7 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64)))], 7) (fixture s 0 7 5) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (7 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (5 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_0_2_0
example (s : riscv_state) : «dfn'SLT» (0,1,2) (fixture s 0 18446744073709551615 0) =
 (let t := fixture s 0 18446744073709551615 0; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))], 0) (fixture s 0 18446744073709551615 0) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_0_2_1
example (s : riscv_state) : «dfn'SLT» (1,1,2) (fixture s 0 18446744073709551615 0) =
 (let t := fixture s 0 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))], 1) (fixture s 0 18446744073709551615 0) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_0_2_2
example (s : riscv_state) : «dfn'SLT» (2,1,2) (fixture s 0 18446744073709551615 0) =
 (let t := fixture s 0 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))], 2) (fixture s 0 18446744073709551615 0) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_0_2_7
example (s : riscv_state) : «dfn'SLT» (7,1,2) (fixture s 0 18446744073709551615 0) =
 (let t := fixture s 0 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))], 7) (fixture s 0 18446744073709551615 0) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_0_3_0
example (s : riscv_state) : «dfn'SLT» (0,1,2) (fixture s 0 0 18446744073709551615) =
 (let t := fixture s 0 0 18446744073709551615; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))], 0) (fixture s 0 0 18446744073709551615) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_0_3_1
example (s : riscv_state) : «dfn'SLT» (1,1,2) (fixture s 0 0 18446744073709551615) =
 (let t := fixture s 0 0 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))], 1) (fixture s 0 0 18446744073709551615) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_0_3_2
example (s : riscv_state) : «dfn'SLT» (2,1,2) (fixture s 0 0 18446744073709551615) =
 (let t := fixture s 0 0 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))], 2) (fixture s 0 0 18446744073709551615) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_0_3_7
example (s : riscv_state) : «dfn'SLT» (7,1,2) (fixture s 0 0 18446744073709551615) =
 (let t := fixture s 0 0 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))], 7) (fixture s 0 0 18446744073709551615) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_0_4_0
example (s : riscv_state) : «dfn'SLT» (0,1,2) (fixture s 0 4294967297 1) =
 (let t := fixture s 0 4294967297 1; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (1 : BitVec 64)))], 0) (fixture s 0 4294967297 1) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (1 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_0_4_1
example (s : riscv_state) : «dfn'SLT» (1,1,2) (fixture s 0 4294967297 1) =
 (let t := fixture s 0 4294967297 1; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (1 : BitVec 64)))], 1) (fixture s 0 4294967297 1) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (1 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_0_4_2
example (s : riscv_state) : «dfn'SLT» (2,1,2) (fixture s 0 4294967297 1) =
 (let t := fixture s 0 4294967297 1; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (1 : BitVec 64)))], 2) (fixture s 0 4294967297 1) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (1 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_0_4_7
example (s : riscv_state) : «dfn'SLT» (7,1,2) (fixture s 0 4294967297 1) =
 (let t := fixture s 0 4294967297 1; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (1 : BitVec 64)))], 7) (fixture s 0 4294967297 1) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (1 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_0_5_0
example (s : riscv_state) : «dfn'SLT» (0,1,2) (fixture s 0 2147483648 1) =
 (let t := fixture s 0 2147483648 1; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (1 : BitVec 64)))], 0) (fixture s 0 2147483648 1) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (1 : BitVec 64)))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_0_5_1
example (s : riscv_state) : «dfn'SLT» (1,1,2) (fixture s 0 2147483648 1) =
 (let t := fixture s 0 2147483648 1; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (1 : BitVec 64)))], 1) (fixture s 0 2147483648 1) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (1 : BitVec 64)))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_0_5_2
example (s : riscv_state) : «dfn'SLT» (2,1,2) (fixture s 0 2147483648 1) =
 (let t := fixture s 0 2147483648 1; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (1 : BitVec 64)))], 2) (fixture s 0 2147483648 1) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (1 : BitVec 64)))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_0_5_7
example (s : riscv_state) : «dfn'SLT» (7,1,2) (fixture s 0 2147483648 1) =
 (let t := fixture s 0 2147483648 1; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (1 : BitVec 64)))], 7) (fixture s 0 2147483648 1) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (1 : BitVec 64)))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_0_6_0
example (s : riscv_state) : «dfn'SLT» (0,1,2) (fixture s 0 9223372036854775808 0) =
 (let t := fixture s 0 9223372036854775808 0; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))], 0) (fixture s 0 9223372036854775808 0) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_0_6_1
example (s : riscv_state) : «dfn'SLT» (1,1,2) (fixture s 0 9223372036854775808 0) =
 (let t := fixture s 0 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))], 1) (fixture s 0 9223372036854775808 0) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_0_6_2
example (s : riscv_state) : «dfn'SLT» (2,1,2) (fixture s 0 9223372036854775808 0) =
 (let t := fixture s 0 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))], 2) (fixture s 0 9223372036854775808 0) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_0_6_7
example (s : riscv_state) : «dfn'SLT» (7,1,2) (fixture s 0 9223372036854775808 0) =
 (let t := fixture s 0 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))], 7) (fixture s 0 9223372036854775808 0) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_0_7_0
example (s : riscv_state) : «dfn'SLT» (0,1,2) (fixture s 0 18446744073709551615 18446744073709551615) =
 (let t := fixture s 0 18446744073709551615 18446744073709551615; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))], 0) (fixture s 0 18446744073709551615 18446744073709551615) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_0_7_1
example (s : riscv_state) : «dfn'SLT» (1,1,2) (fixture s 0 18446744073709551615 18446744073709551615) =
 (let t := fixture s 0 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))], 1) (fixture s 0 18446744073709551615 18446744073709551615) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_0_7_2
example (s : riscv_state) : «dfn'SLT» (2,1,2) (fixture s 0 18446744073709551615 18446744073709551615) =
 (let t := fixture s 0 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))], 2) (fixture s 0 18446744073709551615 18446744073709551615) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_0_7_7
example (s : riscv_state) : «dfn'SLT» (7,1,2) (fixture s 0 18446744073709551615 18446744073709551615) =
 (let t := fixture s 0 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))], 7) (fixture s 0 18446744073709551615 18446744073709551615) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_0_8_0
example (s : riscv_state) : «dfn'SLT» (0,0,2) (fixture s 0 17 19) =
 (let t := fixture s 0 17 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (19 : BitVec 64)))], 0) (fixture s 0 17 19) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (19 : BitVec 64)))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_0_8_1
example (s : riscv_state) : «dfn'SLT» (1,0,2) (fixture s 0 17 19) =
 (let t := fixture s 0 17 19; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (19 : BitVec 64)))], 1) (fixture s 0 17 19) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (19 : BitVec 64)))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_0_8_2
example (s : riscv_state) : «dfn'SLT» (2,0,2) (fixture s 0 17 19) =
 (let t := fixture s 0 17 19; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (19 : BitVec 64)))], 2) (fixture s 0 17 19) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (19 : BitVec 64)))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_0_8_7
example (s : riscv_state) : «dfn'SLT» (7,0,2) (fixture s 0 17 19) =
 (let t := fixture s 0 17 19; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (19 : BitVec 64)))], 7) (fixture s 0 17 19) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (19 : BitVec 64)))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_0_9_0
example (s : riscv_state) : «dfn'SLT» (0,1,0) (fixture s 0 17 19) =
 (let t := fixture s 0 17 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (17 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))], 0) (fixture s 0 17 19) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (17 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_0_9_1
example (s : riscv_state) : «dfn'SLT» (1,1,0) (fixture s 0 17 19) =
 (let t := fixture s 0 17 19; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (17 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))], 1) (fixture s 0 17 19) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (17 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_0_9_2
example (s : riscv_state) : «dfn'SLT» (2,1,0) (fixture s 0 17 19) =
 (let t := fixture s 0 17 19; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (17 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))], 2) (fixture s 0 17 19) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (17 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_0_9_7
example (s : riscv_state) : «dfn'SLT» (7,1,0) (fixture s 0 17 19) =
 (let t := fixture s 0 17 19; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (17 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))], 7) (fixture s 0 17 19) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (17 : BitVec 64))) (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_2_0_0
example (s : riscv_state) : «dfn'SLT» (0,1,2) (fixture s 2 5 7) =
 (let t := fixture s 2 5 7; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (5 : BitVec 64) (7 : BitVec 64)], 0) (fixture s 2 5 7) = _
  have numeric : holV2w 64 [BitVec.slt (5 : BitVec 64) (7 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_2_0_1
example (s : riscv_state) : «dfn'SLT» (1,1,2) (fixture s 2 5 7) =
 (let t := fixture s 2 5 7; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (5 : BitVec 64) (7 : BitVec 64)], 1) (fixture s 2 5 7) = _
  have numeric : holV2w 64 [BitVec.slt (5 : BitVec 64) (7 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_2_0_2
example (s : riscv_state) : «dfn'SLT» (2,1,2) (fixture s 2 5 7) =
 (let t := fixture s 2 5 7; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (5 : BitVec 64) (7 : BitVec 64)], 2) (fixture s 2 5 7) = _
  have numeric : holV2w 64 [BitVec.slt (5 : BitVec 64) (7 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_2_0_7
example (s : riscv_state) : «dfn'SLT» (7,1,2) (fixture s 2 5 7) =
 (let t := fixture s 2 5 7; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (5 : BitVec 64) (7 : BitVec 64)], 7) (fixture s 2 5 7) = _
  have numeric : holV2w 64 [BitVec.slt (5 : BitVec 64) (7 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_2_1_0
example (s : riscv_state) : «dfn'SLT» (0,1,2) (fixture s 2 7 5) =
 (let t := fixture s 2 7 5; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (7 : BitVec 64) (5 : BitVec 64)], 0) (fixture s 2 7 5) = _
  have numeric : holV2w 64 [BitVec.slt (7 : BitVec 64) (5 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_2_1_1
example (s : riscv_state) : «dfn'SLT» (1,1,2) (fixture s 2 7 5) =
 (let t := fixture s 2 7 5; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (7 : BitVec 64) (5 : BitVec 64)], 1) (fixture s 2 7 5) = _
  have numeric : holV2w 64 [BitVec.slt (7 : BitVec 64) (5 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_2_1_2
example (s : riscv_state) : «dfn'SLT» (2,1,2) (fixture s 2 7 5) =
 (let t := fixture s 2 7 5; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (7 : BitVec 64) (5 : BitVec 64)], 2) (fixture s 2 7 5) = _
  have numeric : holV2w 64 [BitVec.slt (7 : BitVec 64) (5 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_2_1_7
example (s : riscv_state) : «dfn'SLT» (7,1,2) (fixture s 2 7 5) =
 (let t := fixture s 2 7 5; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (7 : BitVec 64) (5 : BitVec 64)], 7) (fixture s 2 7 5) = _
  have numeric : holV2w 64 [BitVec.slt (7 : BitVec 64) (5 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_2_2_0
example (s : riscv_state) : «dfn'SLT» (0,1,2) (fixture s 2 18446744073709551615 0) =
 (let t := fixture s 2 18446744073709551615 0; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (18446744073709551615 : BitVec 64) (0 : BitVec 64)], 0) (fixture s 2 18446744073709551615 0) = _
  have numeric : holV2w 64 [BitVec.slt (18446744073709551615 : BitVec 64) (0 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_2_2_1
example (s : riscv_state) : «dfn'SLT» (1,1,2) (fixture s 2 18446744073709551615 0) =
 (let t := fixture s 2 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (18446744073709551615 : BitVec 64) (0 : BitVec 64)], 1) (fixture s 2 18446744073709551615 0) = _
  have numeric : holV2w 64 [BitVec.slt (18446744073709551615 : BitVec 64) (0 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_2_2_2
example (s : riscv_state) : «dfn'SLT» (2,1,2) (fixture s 2 18446744073709551615 0) =
 (let t := fixture s 2 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (18446744073709551615 : BitVec 64) (0 : BitVec 64)], 2) (fixture s 2 18446744073709551615 0) = _
  have numeric : holV2w 64 [BitVec.slt (18446744073709551615 : BitVec 64) (0 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_2_2_7
example (s : riscv_state) : «dfn'SLT» (7,1,2) (fixture s 2 18446744073709551615 0) =
 (let t := fixture s 2 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (18446744073709551615 : BitVec 64) (0 : BitVec 64)], 7) (fixture s 2 18446744073709551615 0) = _
  have numeric : holV2w 64 [BitVec.slt (18446744073709551615 : BitVec 64) (0 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_2_3_0
example (s : riscv_state) : «dfn'SLT» (0,1,2) (fixture s 2 0 18446744073709551615) =
 (let t := fixture s 2 0 18446744073709551615; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (0 : BitVec 64) (18446744073709551615 : BitVec 64)], 0) (fixture s 2 0 18446744073709551615) = _
  have numeric : holV2w 64 [BitVec.slt (0 : BitVec 64) (18446744073709551615 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_2_3_1
example (s : riscv_state) : «dfn'SLT» (1,1,2) (fixture s 2 0 18446744073709551615) =
 (let t := fixture s 2 0 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (0 : BitVec 64) (18446744073709551615 : BitVec 64)], 1) (fixture s 2 0 18446744073709551615) = _
  have numeric : holV2w 64 [BitVec.slt (0 : BitVec 64) (18446744073709551615 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_2_3_2
example (s : riscv_state) : «dfn'SLT» (2,1,2) (fixture s 2 0 18446744073709551615) =
 (let t := fixture s 2 0 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (0 : BitVec 64) (18446744073709551615 : BitVec 64)], 2) (fixture s 2 0 18446744073709551615) = _
  have numeric : holV2w 64 [BitVec.slt (0 : BitVec 64) (18446744073709551615 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_2_3_7
example (s : riscv_state) : «dfn'SLT» (7,1,2) (fixture s 2 0 18446744073709551615) =
 (let t := fixture s 2 0 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (0 : BitVec 64) (18446744073709551615 : BitVec 64)], 7) (fixture s 2 0 18446744073709551615) = _
  have numeric : holV2w 64 [BitVec.slt (0 : BitVec 64) (18446744073709551615 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_2_4_0
example (s : riscv_state) : «dfn'SLT» (0,1,2) (fixture s 2 4294967297 1) =
 (let t := fixture s 2 4294967297 1; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (4294967297 : BitVec 64) (1 : BitVec 64)], 0) (fixture s 2 4294967297 1) = _
  have numeric : holV2w 64 [BitVec.slt (4294967297 : BitVec 64) (1 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_2_4_1
example (s : riscv_state) : «dfn'SLT» (1,1,2) (fixture s 2 4294967297 1) =
 (let t := fixture s 2 4294967297 1; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (4294967297 : BitVec 64) (1 : BitVec 64)], 1) (fixture s 2 4294967297 1) = _
  have numeric : holV2w 64 [BitVec.slt (4294967297 : BitVec 64) (1 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_2_4_2
example (s : riscv_state) : «dfn'SLT» (2,1,2) (fixture s 2 4294967297 1) =
 (let t := fixture s 2 4294967297 1; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (4294967297 : BitVec 64) (1 : BitVec 64)], 2) (fixture s 2 4294967297 1) = _
  have numeric : holV2w 64 [BitVec.slt (4294967297 : BitVec 64) (1 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_2_4_7
example (s : riscv_state) : «dfn'SLT» (7,1,2) (fixture s 2 4294967297 1) =
 (let t := fixture s 2 4294967297 1; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (4294967297 : BitVec 64) (1 : BitVec 64)], 7) (fixture s 2 4294967297 1) = _
  have numeric : holV2w 64 [BitVec.slt (4294967297 : BitVec 64) (1 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_2_5_0
example (s : riscv_state) : «dfn'SLT» (0,1,2) (fixture s 2 2147483648 1) =
 (let t := fixture s 2 2147483648 1; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (2147483648 : BitVec 64) (1 : BitVec 64)], 0) (fixture s 2 2147483648 1) = _
  have numeric : holV2w 64 [BitVec.slt (2147483648 : BitVec 64) (1 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_2_5_1
example (s : riscv_state) : «dfn'SLT» (1,1,2) (fixture s 2 2147483648 1) =
 (let t := fixture s 2 2147483648 1; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (2147483648 : BitVec 64) (1 : BitVec 64)], 1) (fixture s 2 2147483648 1) = _
  have numeric : holV2w 64 [BitVec.slt (2147483648 : BitVec 64) (1 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_2_5_2
example (s : riscv_state) : «dfn'SLT» (2,1,2) (fixture s 2 2147483648 1) =
 (let t := fixture s 2 2147483648 1; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (2147483648 : BitVec 64) (1 : BitVec 64)], 2) (fixture s 2 2147483648 1) = _
  have numeric : holV2w 64 [BitVec.slt (2147483648 : BitVec 64) (1 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_2_5_7
example (s : riscv_state) : «dfn'SLT» (7,1,2) (fixture s 2 2147483648 1) =
 (let t := fixture s 2 2147483648 1; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (2147483648 : BitVec 64) (1 : BitVec 64)], 7) (fixture s 2 2147483648 1) = _
  have numeric : holV2w 64 [BitVec.slt (2147483648 : BitVec 64) (1 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_2_6_0
example (s : riscv_state) : «dfn'SLT» (0,1,2) (fixture s 2 9223372036854775808 0) =
 (let t := fixture s 2 9223372036854775808 0; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (9223372036854775808 : BitVec 64) (0 : BitVec 64)], 0) (fixture s 2 9223372036854775808 0) = _
  have numeric : holV2w 64 [BitVec.slt (9223372036854775808 : BitVec 64) (0 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_2_6_1
example (s : riscv_state) : «dfn'SLT» (1,1,2) (fixture s 2 9223372036854775808 0) =
 (let t := fixture s 2 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (9223372036854775808 : BitVec 64) (0 : BitVec 64)], 1) (fixture s 2 9223372036854775808 0) = _
  have numeric : holV2w 64 [BitVec.slt (9223372036854775808 : BitVec 64) (0 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_2_6_2
example (s : riscv_state) : «dfn'SLT» (2,1,2) (fixture s 2 9223372036854775808 0) =
 (let t := fixture s 2 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (9223372036854775808 : BitVec 64) (0 : BitVec 64)], 2) (fixture s 2 9223372036854775808 0) = _
  have numeric : holV2w 64 [BitVec.slt (9223372036854775808 : BitVec 64) (0 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_2_6_7
example (s : riscv_state) : «dfn'SLT» (7,1,2) (fixture s 2 9223372036854775808 0) =
 (let t := fixture s 2 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (9223372036854775808 : BitVec 64) (0 : BitVec 64)], 7) (fixture s 2 9223372036854775808 0) = _
  have numeric : holV2w 64 [BitVec.slt (9223372036854775808 : BitVec 64) (0 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_2_7_0
example (s : riscv_state) : «dfn'SLT» (0,1,2) (fixture s 2 18446744073709551615 18446744073709551615) =
 (let t := fixture s 2 18446744073709551615 18446744073709551615; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (18446744073709551615 : BitVec 64) (18446744073709551615 : BitVec 64)], 0) (fixture s 2 18446744073709551615 18446744073709551615) = _
  have numeric : holV2w 64 [BitVec.slt (18446744073709551615 : BitVec 64) (18446744073709551615 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_2_7_1
example (s : riscv_state) : «dfn'SLT» (1,1,2) (fixture s 2 18446744073709551615 18446744073709551615) =
 (let t := fixture s 2 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (18446744073709551615 : BitVec 64) (18446744073709551615 : BitVec 64)], 1) (fixture s 2 18446744073709551615 18446744073709551615) = _
  have numeric : holV2w 64 [BitVec.slt (18446744073709551615 : BitVec 64) (18446744073709551615 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_2_7_2
example (s : riscv_state) : «dfn'SLT» (2,1,2) (fixture s 2 18446744073709551615 18446744073709551615) =
 (let t := fixture s 2 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (18446744073709551615 : BitVec 64) (18446744073709551615 : BitVec 64)], 2) (fixture s 2 18446744073709551615 18446744073709551615) = _
  have numeric : holV2w 64 [BitVec.slt (18446744073709551615 : BitVec 64) (18446744073709551615 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_2_7_7
example (s : riscv_state) : «dfn'SLT» (7,1,2) (fixture s 2 18446744073709551615 18446744073709551615) =
 (let t := fixture s 2 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (18446744073709551615 : BitVec 64) (18446744073709551615 : BitVec 64)], 7) (fixture s 2 18446744073709551615 18446744073709551615) = _
  have numeric : holV2w 64 [BitVec.slt (18446744073709551615 : BitVec 64) (18446744073709551615 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_2_8_0
example (s : riscv_state) : «dfn'SLT» (0,0,2) (fixture s 2 17 19) =
 (let t := fixture s 2 17 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (0 : BitVec 64) (19 : BitVec 64)], 0) (fixture s 2 17 19) = _
  have numeric : holV2w 64 [BitVec.slt (0 : BitVec 64) (19 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_2_8_1
example (s : riscv_state) : «dfn'SLT» (1,0,2) (fixture s 2 17 19) =
 (let t := fixture s 2 17 19; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (0 : BitVec 64) (19 : BitVec 64)], 1) (fixture s 2 17 19) = _
  have numeric : holV2w 64 [BitVec.slt (0 : BitVec 64) (19 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_2_8_2
example (s : riscv_state) : «dfn'SLT» (2,0,2) (fixture s 2 17 19) =
 (let t := fixture s 2 17 19; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (0 : BitVec 64) (19 : BitVec 64)], 2) (fixture s 2 17 19) = _
  have numeric : holV2w 64 [BitVec.slt (0 : BitVec 64) (19 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_2_8_7
example (s : riscv_state) : «dfn'SLT» (7,0,2) (fixture s 2 17 19) =
 (let t := fixture s 2 17 19; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (0 : BitVec 64) (19 : BitVec 64)], 7) (fixture s 2 17 19) = _
  have numeric : holV2w 64 [BitVec.slt (0 : BitVec 64) (19 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_2_9_0
example (s : riscv_state) : «dfn'SLT» (0,1,0) (fixture s 2 17 19) =
 (let t := fixture s 2 17 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (17 : BitVec 64) (0 : BitVec 64)], 0) (fixture s 2 17 19) = _
  have numeric : holV2w 64 [BitVec.slt (17 : BitVec 64) (0 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_2_9_1
example (s : riscv_state) : «dfn'SLT» (1,1,0) (fixture s 2 17 19) =
 (let t := fixture s 2 17 19; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (17 : BitVec 64) (0 : BitVec 64)], 1) (fixture s 2 17 19) = _
  have numeric : holV2w 64 [BitVec.slt (17 : BitVec 64) (0 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_2_9_2
example (s : riscv_state) : «dfn'SLT» (2,1,0) (fixture s 2 17 19) =
 (let t := fixture s 2 17 19; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (17 : BitVec 64) (0 : BitVec 64)], 2) (fixture s 2 17 19) = _
  have numeric : holV2w 64 [BitVec.slt (17 : BitVec 64) (0 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_2_9_7
example (s : riscv_state) : «dfn'SLT» (7,1,0) (fixture s 2 17 19) =
 (let t := fixture s 2 17 19; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (17 : BitVec 64) (0 : BitVec 64)], 7) (fixture s 2 17 19) = _
  have numeric : holV2w 64 [BitVec.slt (17 : BitVec 64) (0 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_3_0_0
example (s : riscv_state) : «dfn'SLT» (0,1,2) (fixture s 3 5 7) =
 (let t := fixture s 3 5 7; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (5 : BitVec 64) (7 : BitVec 64)], 0) (fixture s 3 5 7) = _
  have numeric : holV2w 64 [BitVec.slt (5 : BitVec 64) (7 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_3_0_1
example (s : riscv_state) : «dfn'SLT» (1,1,2) (fixture s 3 5 7) =
 (let t := fixture s 3 5 7; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (5 : BitVec 64) (7 : BitVec 64)], 1) (fixture s 3 5 7) = _
  have numeric : holV2w 64 [BitVec.slt (5 : BitVec 64) (7 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_3_0_2
example (s : riscv_state) : «dfn'SLT» (2,1,2) (fixture s 3 5 7) =
 (let t := fixture s 3 5 7; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (5 : BitVec 64) (7 : BitVec 64)], 2) (fixture s 3 5 7) = _
  have numeric : holV2w 64 [BitVec.slt (5 : BitVec 64) (7 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_3_0_7
example (s : riscv_state) : «dfn'SLT» (7,1,2) (fixture s 3 5 7) =
 (let t := fixture s 3 5 7; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (5 : BitVec 64) (7 : BitVec 64)], 7) (fixture s 3 5 7) = _
  have numeric : holV2w 64 [BitVec.slt (5 : BitVec 64) (7 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_3_1_0
example (s : riscv_state) : «dfn'SLT» (0,1,2) (fixture s 3 7 5) =
 (let t := fixture s 3 7 5; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (7 : BitVec 64) (5 : BitVec 64)], 0) (fixture s 3 7 5) = _
  have numeric : holV2w 64 [BitVec.slt (7 : BitVec 64) (5 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_3_1_1
example (s : riscv_state) : «dfn'SLT» (1,1,2) (fixture s 3 7 5) =
 (let t := fixture s 3 7 5; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (7 : BitVec 64) (5 : BitVec 64)], 1) (fixture s 3 7 5) = _
  have numeric : holV2w 64 [BitVec.slt (7 : BitVec 64) (5 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_3_1_2
example (s : riscv_state) : «dfn'SLT» (2,1,2) (fixture s 3 7 5) =
 (let t := fixture s 3 7 5; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (7 : BitVec 64) (5 : BitVec 64)], 2) (fixture s 3 7 5) = _
  have numeric : holV2w 64 [BitVec.slt (7 : BitVec 64) (5 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_3_1_7
example (s : riscv_state) : «dfn'SLT» (7,1,2) (fixture s 3 7 5) =
 (let t := fixture s 3 7 5; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (7 : BitVec 64) (5 : BitVec 64)], 7) (fixture s 3 7 5) = _
  have numeric : holV2w 64 [BitVec.slt (7 : BitVec 64) (5 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_3_2_0
example (s : riscv_state) : «dfn'SLT» (0,1,2) (fixture s 3 18446744073709551615 0) =
 (let t := fixture s 3 18446744073709551615 0; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (18446744073709551615 : BitVec 64) (0 : BitVec 64)], 0) (fixture s 3 18446744073709551615 0) = _
  have numeric : holV2w 64 [BitVec.slt (18446744073709551615 : BitVec 64) (0 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_3_2_1
example (s : riscv_state) : «dfn'SLT» (1,1,2) (fixture s 3 18446744073709551615 0) =
 (let t := fixture s 3 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (18446744073709551615 : BitVec 64) (0 : BitVec 64)], 1) (fixture s 3 18446744073709551615 0) = _
  have numeric : holV2w 64 [BitVec.slt (18446744073709551615 : BitVec 64) (0 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_3_2_2
example (s : riscv_state) : «dfn'SLT» (2,1,2) (fixture s 3 18446744073709551615 0) =
 (let t := fixture s 3 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (18446744073709551615 : BitVec 64) (0 : BitVec 64)], 2) (fixture s 3 18446744073709551615 0) = _
  have numeric : holV2w 64 [BitVec.slt (18446744073709551615 : BitVec 64) (0 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_3_2_7
example (s : riscv_state) : «dfn'SLT» (7,1,2) (fixture s 3 18446744073709551615 0) =
 (let t := fixture s 3 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (18446744073709551615 : BitVec 64) (0 : BitVec 64)], 7) (fixture s 3 18446744073709551615 0) = _
  have numeric : holV2w 64 [BitVec.slt (18446744073709551615 : BitVec 64) (0 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_3_3_0
example (s : riscv_state) : «dfn'SLT» (0,1,2) (fixture s 3 0 18446744073709551615) =
 (let t := fixture s 3 0 18446744073709551615; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (0 : BitVec 64) (18446744073709551615 : BitVec 64)], 0) (fixture s 3 0 18446744073709551615) = _
  have numeric : holV2w 64 [BitVec.slt (0 : BitVec 64) (18446744073709551615 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_3_3_1
example (s : riscv_state) : «dfn'SLT» (1,1,2) (fixture s 3 0 18446744073709551615) =
 (let t := fixture s 3 0 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (0 : BitVec 64) (18446744073709551615 : BitVec 64)], 1) (fixture s 3 0 18446744073709551615) = _
  have numeric : holV2w 64 [BitVec.slt (0 : BitVec 64) (18446744073709551615 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_3_3_2
example (s : riscv_state) : «dfn'SLT» (2,1,2) (fixture s 3 0 18446744073709551615) =
 (let t := fixture s 3 0 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (0 : BitVec 64) (18446744073709551615 : BitVec 64)], 2) (fixture s 3 0 18446744073709551615) = _
  have numeric : holV2w 64 [BitVec.slt (0 : BitVec 64) (18446744073709551615 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_3_3_7
example (s : riscv_state) : «dfn'SLT» (7,1,2) (fixture s 3 0 18446744073709551615) =
 (let t := fixture s 3 0 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (0 : BitVec 64) (18446744073709551615 : BitVec 64)], 7) (fixture s 3 0 18446744073709551615) = _
  have numeric : holV2w 64 [BitVec.slt (0 : BitVec 64) (18446744073709551615 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_3_4_0
example (s : riscv_state) : «dfn'SLT» (0,1,2) (fixture s 3 4294967297 1) =
 (let t := fixture s 3 4294967297 1; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (4294967297 : BitVec 64) (1 : BitVec 64)], 0) (fixture s 3 4294967297 1) = _
  have numeric : holV2w 64 [BitVec.slt (4294967297 : BitVec 64) (1 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_3_4_1
example (s : riscv_state) : «dfn'SLT» (1,1,2) (fixture s 3 4294967297 1) =
 (let t := fixture s 3 4294967297 1; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (4294967297 : BitVec 64) (1 : BitVec 64)], 1) (fixture s 3 4294967297 1) = _
  have numeric : holV2w 64 [BitVec.slt (4294967297 : BitVec 64) (1 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_3_4_2
example (s : riscv_state) : «dfn'SLT» (2,1,2) (fixture s 3 4294967297 1) =
 (let t := fixture s 3 4294967297 1; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (4294967297 : BitVec 64) (1 : BitVec 64)], 2) (fixture s 3 4294967297 1) = _
  have numeric : holV2w 64 [BitVec.slt (4294967297 : BitVec 64) (1 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_3_4_7
example (s : riscv_state) : «dfn'SLT» (7,1,2) (fixture s 3 4294967297 1) =
 (let t := fixture s 3 4294967297 1; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (4294967297 : BitVec 64) (1 : BitVec 64)], 7) (fixture s 3 4294967297 1) = _
  have numeric : holV2w 64 [BitVec.slt (4294967297 : BitVec 64) (1 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_3_5_0
example (s : riscv_state) : «dfn'SLT» (0,1,2) (fixture s 3 2147483648 1) =
 (let t := fixture s 3 2147483648 1; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (2147483648 : BitVec 64) (1 : BitVec 64)], 0) (fixture s 3 2147483648 1) = _
  have numeric : holV2w 64 [BitVec.slt (2147483648 : BitVec 64) (1 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_3_5_1
example (s : riscv_state) : «dfn'SLT» (1,1,2) (fixture s 3 2147483648 1) =
 (let t := fixture s 3 2147483648 1; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (2147483648 : BitVec 64) (1 : BitVec 64)], 1) (fixture s 3 2147483648 1) = _
  have numeric : holV2w 64 [BitVec.slt (2147483648 : BitVec 64) (1 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_3_5_2
example (s : riscv_state) : «dfn'SLT» (2,1,2) (fixture s 3 2147483648 1) =
 (let t := fixture s 3 2147483648 1; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (2147483648 : BitVec 64) (1 : BitVec 64)], 2) (fixture s 3 2147483648 1) = _
  have numeric : holV2w 64 [BitVec.slt (2147483648 : BitVec 64) (1 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_3_5_7
example (s : riscv_state) : «dfn'SLT» (7,1,2) (fixture s 3 2147483648 1) =
 (let t := fixture s 3 2147483648 1; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (2147483648 : BitVec 64) (1 : BitVec 64)], 7) (fixture s 3 2147483648 1) = _
  have numeric : holV2w 64 [BitVec.slt (2147483648 : BitVec 64) (1 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_3_6_0
example (s : riscv_state) : «dfn'SLT» (0,1,2) (fixture s 3 9223372036854775808 0) =
 (let t := fixture s 3 9223372036854775808 0; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (9223372036854775808 : BitVec 64) (0 : BitVec 64)], 0) (fixture s 3 9223372036854775808 0) = _
  have numeric : holV2w 64 [BitVec.slt (9223372036854775808 : BitVec 64) (0 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_3_6_1
example (s : riscv_state) : «dfn'SLT» (1,1,2) (fixture s 3 9223372036854775808 0) =
 (let t := fixture s 3 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (9223372036854775808 : BitVec 64) (0 : BitVec 64)], 1) (fixture s 3 9223372036854775808 0) = _
  have numeric : holV2w 64 [BitVec.slt (9223372036854775808 : BitVec 64) (0 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_3_6_2
example (s : riscv_state) : «dfn'SLT» (2,1,2) (fixture s 3 9223372036854775808 0) =
 (let t := fixture s 3 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (9223372036854775808 : BitVec 64) (0 : BitVec 64)], 2) (fixture s 3 9223372036854775808 0) = _
  have numeric : holV2w 64 [BitVec.slt (9223372036854775808 : BitVec 64) (0 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_3_6_7
example (s : riscv_state) : «dfn'SLT» (7,1,2) (fixture s 3 9223372036854775808 0) =
 (let t := fixture s 3 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (9223372036854775808 : BitVec 64) (0 : BitVec 64)], 7) (fixture s 3 9223372036854775808 0) = _
  have numeric : holV2w 64 [BitVec.slt (9223372036854775808 : BitVec 64) (0 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_3_7_0
example (s : riscv_state) : «dfn'SLT» (0,1,2) (fixture s 3 18446744073709551615 18446744073709551615) =
 (let t := fixture s 3 18446744073709551615 18446744073709551615; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (18446744073709551615 : BitVec 64) (18446744073709551615 : BitVec 64)], 0) (fixture s 3 18446744073709551615 18446744073709551615) = _
  have numeric : holV2w 64 [BitVec.slt (18446744073709551615 : BitVec 64) (18446744073709551615 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_3_7_1
example (s : riscv_state) : «dfn'SLT» (1,1,2) (fixture s 3 18446744073709551615 18446744073709551615) =
 (let t := fixture s 3 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (18446744073709551615 : BitVec 64) (18446744073709551615 : BitVec 64)], 1) (fixture s 3 18446744073709551615 18446744073709551615) = _
  have numeric : holV2w 64 [BitVec.slt (18446744073709551615 : BitVec 64) (18446744073709551615 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_3_7_2
example (s : riscv_state) : «dfn'SLT» (2,1,2) (fixture s 3 18446744073709551615 18446744073709551615) =
 (let t := fixture s 3 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (18446744073709551615 : BitVec 64) (18446744073709551615 : BitVec 64)], 2) (fixture s 3 18446744073709551615 18446744073709551615) = _
  have numeric : holV2w 64 [BitVec.slt (18446744073709551615 : BitVec 64) (18446744073709551615 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_3_7_7
example (s : riscv_state) : «dfn'SLT» (7,1,2) (fixture s 3 18446744073709551615 18446744073709551615) =
 (let t := fixture s 3 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (18446744073709551615 : BitVec 64) (18446744073709551615 : BitVec 64)], 7) (fixture s 3 18446744073709551615 18446744073709551615) = _
  have numeric : holV2w 64 [BitVec.slt (18446744073709551615 : BitVec 64) (18446744073709551615 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_3_8_0
example (s : riscv_state) : «dfn'SLT» (0,0,2) (fixture s 3 17 19) =
 (let t := fixture s 3 17 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (0 : BitVec 64) (19 : BitVec 64)], 0) (fixture s 3 17 19) = _
  have numeric : holV2w 64 [BitVec.slt (0 : BitVec 64) (19 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_3_8_1
example (s : riscv_state) : «dfn'SLT» (1,0,2) (fixture s 3 17 19) =
 (let t := fixture s 3 17 19; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (0 : BitVec 64) (19 : BitVec 64)], 1) (fixture s 3 17 19) = _
  have numeric : holV2w 64 [BitVec.slt (0 : BitVec 64) (19 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_3_8_2
example (s : riscv_state) : «dfn'SLT» (2,0,2) (fixture s 3 17 19) =
 (let t := fixture s 3 17 19; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (0 : BitVec 64) (19 : BitVec 64)], 2) (fixture s 3 17 19) = _
  have numeric : holV2w 64 [BitVec.slt (0 : BitVec 64) (19 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_3_8_7
example (s : riscv_state) : «dfn'SLT» (7,0,2) (fixture s 3 17 19) =
 (let t := fixture s 3 17 19; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (0 : BitVec 64) (19 : BitVec 64)], 7) (fixture s 3 17 19) = _
  have numeric : holV2w 64 [BitVec.slt (0 : BitVec 64) (19 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_3_9_0
example (s : riscv_state) : «dfn'SLT» (0,1,0) (fixture s 3 17 19) =
 (let t := fixture s 3 17 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (17 : BitVec 64) (0 : BitVec 64)], 0) (fixture s 3 17 19) = _
  have numeric : holV2w 64 [BitVec.slt (17 : BitVec 64) (0 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_3_9_1
example (s : riscv_state) : «dfn'SLT» (1,1,0) (fixture s 3 17 19) =
 (let t := fixture s 3 17 19; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (17 : BitVec 64) (0 : BitVec 64)], 1) (fixture s 3 17 19) = _
  have numeric : holV2w 64 [BitVec.slt (17 : BitVec 64) (0 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_3_9_2
example (s : riscv_state) : «dfn'SLT» (2,1,0) (fixture s 3 17 19) =
 (let t := fixture s 3 17 19; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (17 : BitVec 64) (0 : BitVec 64)], 2) (fixture s 3 17 19) = _
  have numeric : holV2w 64 [BitVec.slt (17 : BitVec 64) (0 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLT_3_9_7
example (s : riscv_state) : «dfn'SLT» (7,1,0) (fixture s 3 17 19) =
 (let t := fixture s 3 17 19; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (17 : BitVec 64) (0 : BitVec 64)], 7) (fixture s 3 17 19) = _
  have numeric : holV2w 64 [BitVec.slt (17 : BitVec 64) (0 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_0_0_0
example (s : riscv_state) : «dfn'SLTU» (0,1,2) (fixture s 0 5 7) =
 (let t := fixture s 0 5 7; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (5 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (7 : BitVec 64)))], 0) (fixture s 0 5 7) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (5 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (7 : BitVec 64)))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_0_0_1
example (s : riscv_state) : «dfn'SLTU» (1,1,2) (fixture s 0 5 7) =
 (let t := fixture s 0 5 7; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (5 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (7 : BitVec 64)))], 1) (fixture s 0 5 7) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (5 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (7 : BitVec 64)))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_0_0_2
example (s : riscv_state) : «dfn'SLTU» (2,1,2) (fixture s 0 5 7) =
 (let t := fixture s 0 5 7; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (5 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (7 : BitVec 64)))], 2) (fixture s 0 5 7) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (5 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (7 : BitVec 64)))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_0_0_7
example (s : riscv_state) : «dfn'SLTU» (7,1,2) (fixture s 0 5 7) =
 (let t := fixture s 0 5 7; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (5 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (7 : BitVec 64)))], 7) (fixture s 0 5 7) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (5 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (7 : BitVec 64)))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_0_1_0
example (s : riscv_state) : «dfn'SLTU» (0,1,2) (fixture s 0 7 5) =
 (let t := fixture s 0 7 5; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (7 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (5 : BitVec 64)))], 0) (fixture s 0 7 5) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (7 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (5 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_0_1_1
example (s : riscv_state) : «dfn'SLTU» (1,1,2) (fixture s 0 7 5) =
 (let t := fixture s 0 7 5; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (7 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (5 : BitVec 64)))], 1) (fixture s 0 7 5) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (7 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (5 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_0_1_2
example (s : riscv_state) : «dfn'SLTU» (2,1,2) (fixture s 0 7 5) =
 (let t := fixture s 0 7 5; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (7 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (5 : BitVec 64)))], 2) (fixture s 0 7 5) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (7 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (5 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_0_1_7
example (s : riscv_state) : «dfn'SLTU» (7,1,2) (fixture s 0 7 5) =
 (let t := fixture s 0 7 5; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (7 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (5 : BitVec 64)))], 7) (fixture s 0 7 5) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (7 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (5 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_0_2_0
example (s : riscv_state) : «dfn'SLTU» (0,1,2) (fixture s 0 18446744073709551615 0) =
 (let t := fixture s 0 18446744073709551615 0; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64)))], 0) (fixture s 0 18446744073709551615 0) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_0_2_1
example (s : riscv_state) : «dfn'SLTU» (1,1,2) (fixture s 0 18446744073709551615 0) =
 (let t := fixture s 0 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64)))], 1) (fixture s 0 18446744073709551615 0) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_0_2_2
example (s : riscv_state) : «dfn'SLTU» (2,1,2) (fixture s 0 18446744073709551615 0) =
 (let t := fixture s 0 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64)))], 2) (fixture s 0 18446744073709551615 0) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_0_2_7
example (s : riscv_state) : «dfn'SLTU» (7,1,2) (fixture s 0 18446744073709551615 0) =
 (let t := fixture s 0 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64)))], 7) (fixture s 0 18446744073709551615 0) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_0_3_0
example (s : riscv_state) : «dfn'SLTU» (0,1,2) (fixture s 0 0 18446744073709551615) =
 (let t := fixture s 0 0 18446744073709551615; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))], 0) (fixture s 0 0 18446744073709551615) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_0_3_1
example (s : riscv_state) : «dfn'SLTU» (1,1,2) (fixture s 0 0 18446744073709551615) =
 (let t := fixture s 0 0 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))], 1) (fixture s 0 0 18446744073709551615) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_0_3_2
example (s : riscv_state) : «dfn'SLTU» (2,1,2) (fixture s 0 0 18446744073709551615) =
 (let t := fixture s 0 0 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))], 2) (fixture s 0 0 18446744073709551615) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_0_3_7
example (s : riscv_state) : «dfn'SLTU» (7,1,2) (fixture s 0 0 18446744073709551615) =
 (let t := fixture s 0 0 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))], 7) (fixture s 0 0 18446744073709551615) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_0_4_0
example (s : riscv_state) : «dfn'SLTU» (0,1,2) (fixture s 0 4294967297 1) =
 (let t := fixture s 0 4294967297 1; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (1 : BitVec 64)))], 0) (fixture s 0 4294967297 1) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (1 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_0_4_1
example (s : riscv_state) : «dfn'SLTU» (1,1,2) (fixture s 0 4294967297 1) =
 (let t := fixture s 0 4294967297 1; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (1 : BitVec 64)))], 1) (fixture s 0 4294967297 1) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (1 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_0_4_2
example (s : riscv_state) : «dfn'SLTU» (2,1,2) (fixture s 0 4294967297 1) =
 (let t := fixture s 0 4294967297 1; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (1 : BitVec 64)))], 2) (fixture s 0 4294967297 1) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (1 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_0_4_7
example (s : riscv_state) : «dfn'SLTU» (7,1,2) (fixture s 0 4294967297 1) =
 (let t := fixture s 0 4294967297 1; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (1 : BitVec 64)))], 7) (fixture s 0 4294967297 1) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (1 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_0_5_0
example (s : riscv_state) : «dfn'SLTU» (0,1,2) (fixture s 0 2147483648 1) =
 (let t := fixture s 0 2147483648 1; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (1 : BitVec 64)))], 0) (fixture s 0 2147483648 1) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (1 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_0_5_1
example (s : riscv_state) : «dfn'SLTU» (1,1,2) (fixture s 0 2147483648 1) =
 (let t := fixture s 0 2147483648 1; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (1 : BitVec 64)))], 1) (fixture s 0 2147483648 1) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (1 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_0_5_2
example (s : riscv_state) : «dfn'SLTU» (2,1,2) (fixture s 0 2147483648 1) =
 (let t := fixture s 0 2147483648 1; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (1 : BitVec 64)))], 2) (fixture s 0 2147483648 1) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (1 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_0_5_7
example (s : riscv_state) : «dfn'SLTU» (7,1,2) (fixture s 0 2147483648 1) =
 (let t := fixture s 0 2147483648 1; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (1 : BitVec 64)))], 7) (fixture s 0 2147483648 1) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (1 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_0_6_0
example (s : riscv_state) : «dfn'SLTU» (0,1,2) (fixture s 0 9223372036854775808 0) =
 (let t := fixture s 0 9223372036854775808 0; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64)))], 0) (fixture s 0 9223372036854775808 0) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_0_6_1
example (s : riscv_state) : «dfn'SLTU» (1,1,2) (fixture s 0 9223372036854775808 0) =
 (let t := fixture s 0 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64)))], 1) (fixture s 0 9223372036854775808 0) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_0_6_2
example (s : riscv_state) : «dfn'SLTU» (2,1,2) (fixture s 0 9223372036854775808 0) =
 (let t := fixture s 0 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64)))], 2) (fixture s 0 9223372036854775808 0) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_0_6_7
example (s : riscv_state) : «dfn'SLTU» (7,1,2) (fixture s 0 9223372036854775808 0) =
 (let t := fixture s 0 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64)))], 7) (fixture s 0 9223372036854775808 0) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_0_7_0
example (s : riscv_state) : «dfn'SLTU» (0,1,2) (fixture s 0 18446744073709551615 18446744073709551615) =
 (let t := fixture s 0 18446744073709551615 18446744073709551615; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))], 0) (fixture s 0 18446744073709551615 18446744073709551615) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_0_7_1
example (s : riscv_state) : «dfn'SLTU» (1,1,2) (fixture s 0 18446744073709551615 18446744073709551615) =
 (let t := fixture s 0 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))], 1) (fixture s 0 18446744073709551615 18446744073709551615) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_0_7_2
example (s : riscv_state) : «dfn'SLTU» (2,1,2) (fixture s 0 18446744073709551615 18446744073709551615) =
 (let t := fixture s 0 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))], 2) (fixture s 0 18446744073709551615 18446744073709551615) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_0_7_7
example (s : riscv_state) : «dfn'SLTU» (7,1,2) (fixture s 0 18446744073709551615 18446744073709551615) =
 (let t := fixture s 0 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))], 7) (fixture s 0 18446744073709551615 18446744073709551615) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_0_8_0
example (s : riscv_state) : «dfn'SLTU» (0,0,2) (fixture s 0 17 19) =
 (let t := fixture s 0 17 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (19 : BitVec 64)))], 0) (fixture s 0 17 19) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (19 : BitVec 64)))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_0_8_1
example (s : riscv_state) : «dfn'SLTU» (1,0,2) (fixture s 0 17 19) =
 (let t := fixture s 0 17 19; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (19 : BitVec 64)))], 1) (fixture s 0 17 19) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (19 : BitVec 64)))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_0_8_2
example (s : riscv_state) : «dfn'SLTU» (2,0,2) (fixture s 0 17 19) =
 (let t := fixture s 0 17 19; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (19 : BitVec 64)))], 2) (fixture s 0 17 19) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (19 : BitVec 64)))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_0_8_7
example (s : riscv_state) : «dfn'SLTU» (7,0,2) (fixture s 0 17 19) =
 (let t := fixture s 0 17 19; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (19 : BitVec 64)))], 7) (fixture s 0 17 19) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (19 : BitVec 64)))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_0_9_0
example (s : riscv_state) : «dfn'SLTU» (0,1,0) (fixture s 0 17 19) =
 (let t := fixture s 0 17 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (17 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64)))], 0) (fixture s 0 17 19) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (17 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_0_9_1
example (s : riscv_state) : «dfn'SLTU» (1,1,0) (fixture s 0 17 19) =
 (let t := fixture s 0 17 19; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (17 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64)))], 1) (fixture s 0 17 19) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (17 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_0_9_2
example (s : riscv_state) : «dfn'SLTU» (2,1,0) (fixture s 0 17 19) =
 (let t := fixture s 0 17 19; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (17 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64)))], 2) (fixture s 0 17 19) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (17 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_0_9_7
example (s : riscv_state) : «dfn'SLTU» (7,1,0) (fixture s 0 17 19) =
 (let t := fixture s 0 17 19; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (17 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64)))], 7) (fixture s 0 17 19) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.setWidth 64 (holWordExtract 32 31 0 (17 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64)))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_2_0_0
example (s : riscv_state) : «dfn'SLTU» (0,1,2) (fixture s 2 5 7) =
 (let t := fixture s 2 5 7; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (5 : BitVec 64) (7 : BitVec 64)], 0) (fixture s 2 5 7) = _
  have numeric : holV2w 64 [BitVec.ult (5 : BitVec 64) (7 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_2_0_1
example (s : riscv_state) : «dfn'SLTU» (1,1,2) (fixture s 2 5 7) =
 (let t := fixture s 2 5 7; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (5 : BitVec 64) (7 : BitVec 64)], 1) (fixture s 2 5 7) = _
  have numeric : holV2w 64 [BitVec.ult (5 : BitVec 64) (7 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_2_0_2
example (s : riscv_state) : «dfn'SLTU» (2,1,2) (fixture s 2 5 7) =
 (let t := fixture s 2 5 7; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (5 : BitVec 64) (7 : BitVec 64)], 2) (fixture s 2 5 7) = _
  have numeric : holV2w 64 [BitVec.ult (5 : BitVec 64) (7 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_2_0_7
example (s : riscv_state) : «dfn'SLTU» (7,1,2) (fixture s 2 5 7) =
 (let t := fixture s 2 5 7; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (5 : BitVec 64) (7 : BitVec 64)], 7) (fixture s 2 5 7) = _
  have numeric : holV2w 64 [BitVec.ult (5 : BitVec 64) (7 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_2_1_0
example (s : riscv_state) : «dfn'SLTU» (0,1,2) (fixture s 2 7 5) =
 (let t := fixture s 2 7 5; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (7 : BitVec 64) (5 : BitVec 64)], 0) (fixture s 2 7 5) = _
  have numeric : holV2w 64 [BitVec.ult (7 : BitVec 64) (5 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_2_1_1
example (s : riscv_state) : «dfn'SLTU» (1,1,2) (fixture s 2 7 5) =
 (let t := fixture s 2 7 5; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (7 : BitVec 64) (5 : BitVec 64)], 1) (fixture s 2 7 5) = _
  have numeric : holV2w 64 [BitVec.ult (7 : BitVec 64) (5 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_2_1_2
example (s : riscv_state) : «dfn'SLTU» (2,1,2) (fixture s 2 7 5) =
 (let t := fixture s 2 7 5; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (7 : BitVec 64) (5 : BitVec 64)], 2) (fixture s 2 7 5) = _
  have numeric : holV2w 64 [BitVec.ult (7 : BitVec 64) (5 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_2_1_7
example (s : riscv_state) : «dfn'SLTU» (7,1,2) (fixture s 2 7 5) =
 (let t := fixture s 2 7 5; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (7 : BitVec 64) (5 : BitVec 64)], 7) (fixture s 2 7 5) = _
  have numeric : holV2w 64 [BitVec.ult (7 : BitVec 64) (5 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_2_2_0
example (s : riscv_state) : «dfn'SLTU» (0,1,2) (fixture s 2 18446744073709551615 0) =
 (let t := fixture s 2 18446744073709551615 0; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (18446744073709551615 : BitVec 64) (0 : BitVec 64)], 0) (fixture s 2 18446744073709551615 0) = _
  have numeric : holV2w 64 [BitVec.ult (18446744073709551615 : BitVec 64) (0 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_2_2_1
example (s : riscv_state) : «dfn'SLTU» (1,1,2) (fixture s 2 18446744073709551615 0) =
 (let t := fixture s 2 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (18446744073709551615 : BitVec 64) (0 : BitVec 64)], 1) (fixture s 2 18446744073709551615 0) = _
  have numeric : holV2w 64 [BitVec.ult (18446744073709551615 : BitVec 64) (0 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_2_2_2
example (s : riscv_state) : «dfn'SLTU» (2,1,2) (fixture s 2 18446744073709551615 0) =
 (let t := fixture s 2 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (18446744073709551615 : BitVec 64) (0 : BitVec 64)], 2) (fixture s 2 18446744073709551615 0) = _
  have numeric : holV2w 64 [BitVec.ult (18446744073709551615 : BitVec 64) (0 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_2_2_7
example (s : riscv_state) : «dfn'SLTU» (7,1,2) (fixture s 2 18446744073709551615 0) =
 (let t := fixture s 2 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (18446744073709551615 : BitVec 64) (0 : BitVec 64)], 7) (fixture s 2 18446744073709551615 0) = _
  have numeric : holV2w 64 [BitVec.ult (18446744073709551615 : BitVec 64) (0 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_2_3_0
example (s : riscv_state) : «dfn'SLTU» (0,1,2) (fixture s 2 0 18446744073709551615) =
 (let t := fixture s 2 0 18446744073709551615; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (0 : BitVec 64) (18446744073709551615 : BitVec 64)], 0) (fixture s 2 0 18446744073709551615) = _
  have numeric : holV2w 64 [BitVec.ult (0 : BitVec 64) (18446744073709551615 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_2_3_1
example (s : riscv_state) : «dfn'SLTU» (1,1,2) (fixture s 2 0 18446744073709551615) =
 (let t := fixture s 2 0 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (0 : BitVec 64) (18446744073709551615 : BitVec 64)], 1) (fixture s 2 0 18446744073709551615) = _
  have numeric : holV2w 64 [BitVec.ult (0 : BitVec 64) (18446744073709551615 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_2_3_2
example (s : riscv_state) : «dfn'SLTU» (2,1,2) (fixture s 2 0 18446744073709551615) =
 (let t := fixture s 2 0 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (0 : BitVec 64) (18446744073709551615 : BitVec 64)], 2) (fixture s 2 0 18446744073709551615) = _
  have numeric : holV2w 64 [BitVec.ult (0 : BitVec 64) (18446744073709551615 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_2_3_7
example (s : riscv_state) : «dfn'SLTU» (7,1,2) (fixture s 2 0 18446744073709551615) =
 (let t := fixture s 2 0 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (0 : BitVec 64) (18446744073709551615 : BitVec 64)], 7) (fixture s 2 0 18446744073709551615) = _
  have numeric : holV2w 64 [BitVec.ult (0 : BitVec 64) (18446744073709551615 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_2_4_0
example (s : riscv_state) : «dfn'SLTU» (0,1,2) (fixture s 2 4294967297 1) =
 (let t := fixture s 2 4294967297 1; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (4294967297 : BitVec 64) (1 : BitVec 64)], 0) (fixture s 2 4294967297 1) = _
  have numeric : holV2w 64 [BitVec.ult (4294967297 : BitVec 64) (1 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_2_4_1
example (s : riscv_state) : «dfn'SLTU» (1,1,2) (fixture s 2 4294967297 1) =
 (let t := fixture s 2 4294967297 1; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (4294967297 : BitVec 64) (1 : BitVec 64)], 1) (fixture s 2 4294967297 1) = _
  have numeric : holV2w 64 [BitVec.ult (4294967297 : BitVec 64) (1 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_2_4_2
example (s : riscv_state) : «dfn'SLTU» (2,1,2) (fixture s 2 4294967297 1) =
 (let t := fixture s 2 4294967297 1; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (4294967297 : BitVec 64) (1 : BitVec 64)], 2) (fixture s 2 4294967297 1) = _
  have numeric : holV2w 64 [BitVec.ult (4294967297 : BitVec 64) (1 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_2_4_7
example (s : riscv_state) : «dfn'SLTU» (7,1,2) (fixture s 2 4294967297 1) =
 (let t := fixture s 2 4294967297 1; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (4294967297 : BitVec 64) (1 : BitVec 64)], 7) (fixture s 2 4294967297 1) = _
  have numeric : holV2w 64 [BitVec.ult (4294967297 : BitVec 64) (1 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_2_5_0
example (s : riscv_state) : «dfn'SLTU» (0,1,2) (fixture s 2 2147483648 1) =
 (let t := fixture s 2 2147483648 1; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (2147483648 : BitVec 64) (1 : BitVec 64)], 0) (fixture s 2 2147483648 1) = _
  have numeric : holV2w 64 [BitVec.ult (2147483648 : BitVec 64) (1 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_2_5_1
example (s : riscv_state) : «dfn'SLTU» (1,1,2) (fixture s 2 2147483648 1) =
 (let t := fixture s 2 2147483648 1; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (2147483648 : BitVec 64) (1 : BitVec 64)], 1) (fixture s 2 2147483648 1) = _
  have numeric : holV2w 64 [BitVec.ult (2147483648 : BitVec 64) (1 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_2_5_2
example (s : riscv_state) : «dfn'SLTU» (2,1,2) (fixture s 2 2147483648 1) =
 (let t := fixture s 2 2147483648 1; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (2147483648 : BitVec 64) (1 : BitVec 64)], 2) (fixture s 2 2147483648 1) = _
  have numeric : holV2w 64 [BitVec.ult (2147483648 : BitVec 64) (1 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_2_5_7
example (s : riscv_state) : «dfn'SLTU» (7,1,2) (fixture s 2 2147483648 1) =
 (let t := fixture s 2 2147483648 1; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (2147483648 : BitVec 64) (1 : BitVec 64)], 7) (fixture s 2 2147483648 1) = _
  have numeric : holV2w 64 [BitVec.ult (2147483648 : BitVec 64) (1 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_2_6_0
example (s : riscv_state) : «dfn'SLTU» (0,1,2) (fixture s 2 9223372036854775808 0) =
 (let t := fixture s 2 9223372036854775808 0; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (9223372036854775808 : BitVec 64) (0 : BitVec 64)], 0) (fixture s 2 9223372036854775808 0) = _
  have numeric : holV2w 64 [BitVec.ult (9223372036854775808 : BitVec 64) (0 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_2_6_1
example (s : riscv_state) : «dfn'SLTU» (1,1,2) (fixture s 2 9223372036854775808 0) =
 (let t := fixture s 2 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (9223372036854775808 : BitVec 64) (0 : BitVec 64)], 1) (fixture s 2 9223372036854775808 0) = _
  have numeric : holV2w 64 [BitVec.ult (9223372036854775808 : BitVec 64) (0 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_2_6_2
example (s : riscv_state) : «dfn'SLTU» (2,1,2) (fixture s 2 9223372036854775808 0) =
 (let t := fixture s 2 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (9223372036854775808 : BitVec 64) (0 : BitVec 64)], 2) (fixture s 2 9223372036854775808 0) = _
  have numeric : holV2w 64 [BitVec.ult (9223372036854775808 : BitVec 64) (0 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_2_6_7
example (s : riscv_state) : «dfn'SLTU» (7,1,2) (fixture s 2 9223372036854775808 0) =
 (let t := fixture s 2 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (9223372036854775808 : BitVec 64) (0 : BitVec 64)], 7) (fixture s 2 9223372036854775808 0) = _
  have numeric : holV2w 64 [BitVec.ult (9223372036854775808 : BitVec 64) (0 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_2_7_0
example (s : riscv_state) : «dfn'SLTU» (0,1,2) (fixture s 2 18446744073709551615 18446744073709551615) =
 (let t := fixture s 2 18446744073709551615 18446744073709551615; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (18446744073709551615 : BitVec 64) (18446744073709551615 : BitVec 64)], 0) (fixture s 2 18446744073709551615 18446744073709551615) = _
  have numeric : holV2w 64 [BitVec.ult (18446744073709551615 : BitVec 64) (18446744073709551615 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_2_7_1
example (s : riscv_state) : «dfn'SLTU» (1,1,2) (fixture s 2 18446744073709551615 18446744073709551615) =
 (let t := fixture s 2 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (18446744073709551615 : BitVec 64) (18446744073709551615 : BitVec 64)], 1) (fixture s 2 18446744073709551615 18446744073709551615) = _
  have numeric : holV2w 64 [BitVec.ult (18446744073709551615 : BitVec 64) (18446744073709551615 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_2_7_2
example (s : riscv_state) : «dfn'SLTU» (2,1,2) (fixture s 2 18446744073709551615 18446744073709551615) =
 (let t := fixture s 2 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (18446744073709551615 : BitVec 64) (18446744073709551615 : BitVec 64)], 2) (fixture s 2 18446744073709551615 18446744073709551615) = _
  have numeric : holV2w 64 [BitVec.ult (18446744073709551615 : BitVec 64) (18446744073709551615 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_2_7_7
example (s : riscv_state) : «dfn'SLTU» (7,1,2) (fixture s 2 18446744073709551615 18446744073709551615) =
 (let t := fixture s 2 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (18446744073709551615 : BitVec 64) (18446744073709551615 : BitVec 64)], 7) (fixture s 2 18446744073709551615 18446744073709551615) = _
  have numeric : holV2w 64 [BitVec.ult (18446744073709551615 : BitVec 64) (18446744073709551615 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_2_8_0
example (s : riscv_state) : «dfn'SLTU» (0,0,2) (fixture s 2 17 19) =
 (let t := fixture s 2 17 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (0 : BitVec 64) (19 : BitVec 64)], 0) (fixture s 2 17 19) = _
  have numeric : holV2w 64 [BitVec.ult (0 : BitVec 64) (19 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_2_8_1
example (s : riscv_state) : «dfn'SLTU» (1,0,2) (fixture s 2 17 19) =
 (let t := fixture s 2 17 19; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (0 : BitVec 64) (19 : BitVec 64)], 1) (fixture s 2 17 19) = _
  have numeric : holV2w 64 [BitVec.ult (0 : BitVec 64) (19 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_2_8_2
example (s : riscv_state) : «dfn'SLTU» (2,0,2) (fixture s 2 17 19) =
 (let t := fixture s 2 17 19; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (0 : BitVec 64) (19 : BitVec 64)], 2) (fixture s 2 17 19) = _
  have numeric : holV2w 64 [BitVec.ult (0 : BitVec 64) (19 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_2_8_7
example (s : riscv_state) : «dfn'SLTU» (7,0,2) (fixture s 2 17 19) =
 (let t := fixture s 2 17 19; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (0 : BitVec 64) (19 : BitVec 64)], 7) (fixture s 2 17 19) = _
  have numeric : holV2w 64 [BitVec.ult (0 : BitVec 64) (19 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_2_9_0
example (s : riscv_state) : «dfn'SLTU» (0,1,0) (fixture s 2 17 19) =
 (let t := fixture s 2 17 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (17 : BitVec 64) (0 : BitVec 64)], 0) (fixture s 2 17 19) = _
  have numeric : holV2w 64 [BitVec.ult (17 : BitVec 64) (0 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_2_9_1
example (s : riscv_state) : «dfn'SLTU» (1,1,0) (fixture s 2 17 19) =
 (let t := fixture s 2 17 19; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (17 : BitVec 64) (0 : BitVec 64)], 1) (fixture s 2 17 19) = _
  have numeric : holV2w 64 [BitVec.ult (17 : BitVec 64) (0 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_2_9_2
example (s : riscv_state) : «dfn'SLTU» (2,1,0) (fixture s 2 17 19) =
 (let t := fixture s 2 17 19; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (17 : BitVec 64) (0 : BitVec 64)], 2) (fixture s 2 17 19) = _
  have numeric : holV2w 64 [BitVec.ult (17 : BitVec 64) (0 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_2_9_7
example (s : riscv_state) : «dfn'SLTU» (7,1,0) (fixture s 2 17 19) =
 (let t := fixture s 2 17 19; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (17 : BitVec 64) (0 : BitVec 64)], 7) (fixture s 2 17 19) = _
  have numeric : holV2w 64 [BitVec.ult (17 : BitVec 64) (0 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_3_0_0
example (s : riscv_state) : «dfn'SLTU» (0,1,2) (fixture s 3 5 7) =
 (let t := fixture s 3 5 7; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (5 : BitVec 64) (7 : BitVec 64)], 0) (fixture s 3 5 7) = _
  have numeric : holV2w 64 [BitVec.ult (5 : BitVec 64) (7 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_3_0_1
example (s : riscv_state) : «dfn'SLTU» (1,1,2) (fixture s 3 5 7) =
 (let t := fixture s 3 5 7; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (5 : BitVec 64) (7 : BitVec 64)], 1) (fixture s 3 5 7) = _
  have numeric : holV2w 64 [BitVec.ult (5 : BitVec 64) (7 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_3_0_2
example (s : riscv_state) : «dfn'SLTU» (2,1,2) (fixture s 3 5 7) =
 (let t := fixture s 3 5 7; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (5 : BitVec 64) (7 : BitVec 64)], 2) (fixture s 3 5 7) = _
  have numeric : holV2w 64 [BitVec.ult (5 : BitVec 64) (7 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_3_0_7
example (s : riscv_state) : «dfn'SLTU» (7,1,2) (fixture s 3 5 7) =
 (let t := fixture s 3 5 7; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (5 : BitVec 64) (7 : BitVec 64)], 7) (fixture s 3 5 7) = _
  have numeric : holV2w 64 [BitVec.ult (5 : BitVec 64) (7 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_3_1_0
example (s : riscv_state) : «dfn'SLTU» (0,1,2) (fixture s 3 7 5) =
 (let t := fixture s 3 7 5; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (7 : BitVec 64) (5 : BitVec 64)], 0) (fixture s 3 7 5) = _
  have numeric : holV2w 64 [BitVec.ult (7 : BitVec 64) (5 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_3_1_1
example (s : riscv_state) : «dfn'SLTU» (1,1,2) (fixture s 3 7 5) =
 (let t := fixture s 3 7 5; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (7 : BitVec 64) (5 : BitVec 64)], 1) (fixture s 3 7 5) = _
  have numeric : holV2w 64 [BitVec.ult (7 : BitVec 64) (5 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_3_1_2
example (s : riscv_state) : «dfn'SLTU» (2,1,2) (fixture s 3 7 5) =
 (let t := fixture s 3 7 5; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (7 : BitVec 64) (5 : BitVec 64)], 2) (fixture s 3 7 5) = _
  have numeric : holV2w 64 [BitVec.ult (7 : BitVec 64) (5 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_3_1_7
example (s : riscv_state) : «dfn'SLTU» (7,1,2) (fixture s 3 7 5) =
 (let t := fixture s 3 7 5; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (7 : BitVec 64) (5 : BitVec 64)], 7) (fixture s 3 7 5) = _
  have numeric : holV2w 64 [BitVec.ult (7 : BitVec 64) (5 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_3_2_0
example (s : riscv_state) : «dfn'SLTU» (0,1,2) (fixture s 3 18446744073709551615 0) =
 (let t := fixture s 3 18446744073709551615 0; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (18446744073709551615 : BitVec 64) (0 : BitVec 64)], 0) (fixture s 3 18446744073709551615 0) = _
  have numeric : holV2w 64 [BitVec.ult (18446744073709551615 : BitVec 64) (0 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_3_2_1
example (s : riscv_state) : «dfn'SLTU» (1,1,2) (fixture s 3 18446744073709551615 0) =
 (let t := fixture s 3 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (18446744073709551615 : BitVec 64) (0 : BitVec 64)], 1) (fixture s 3 18446744073709551615 0) = _
  have numeric : holV2w 64 [BitVec.ult (18446744073709551615 : BitVec 64) (0 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_3_2_2
example (s : riscv_state) : «dfn'SLTU» (2,1,2) (fixture s 3 18446744073709551615 0) =
 (let t := fixture s 3 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (18446744073709551615 : BitVec 64) (0 : BitVec 64)], 2) (fixture s 3 18446744073709551615 0) = _
  have numeric : holV2w 64 [BitVec.ult (18446744073709551615 : BitVec 64) (0 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_3_2_7
example (s : riscv_state) : «dfn'SLTU» (7,1,2) (fixture s 3 18446744073709551615 0) =
 (let t := fixture s 3 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (18446744073709551615 : BitVec 64) (0 : BitVec 64)], 7) (fixture s 3 18446744073709551615 0) = _
  have numeric : holV2w 64 [BitVec.ult (18446744073709551615 : BitVec 64) (0 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_3_3_0
example (s : riscv_state) : «dfn'SLTU» (0,1,2) (fixture s 3 0 18446744073709551615) =
 (let t := fixture s 3 0 18446744073709551615; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (0 : BitVec 64) (18446744073709551615 : BitVec 64)], 0) (fixture s 3 0 18446744073709551615) = _
  have numeric : holV2w 64 [BitVec.ult (0 : BitVec 64) (18446744073709551615 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_3_3_1
example (s : riscv_state) : «dfn'SLTU» (1,1,2) (fixture s 3 0 18446744073709551615) =
 (let t := fixture s 3 0 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (0 : BitVec 64) (18446744073709551615 : BitVec 64)], 1) (fixture s 3 0 18446744073709551615) = _
  have numeric : holV2w 64 [BitVec.ult (0 : BitVec 64) (18446744073709551615 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_3_3_2
example (s : riscv_state) : «dfn'SLTU» (2,1,2) (fixture s 3 0 18446744073709551615) =
 (let t := fixture s 3 0 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (0 : BitVec 64) (18446744073709551615 : BitVec 64)], 2) (fixture s 3 0 18446744073709551615) = _
  have numeric : holV2w 64 [BitVec.ult (0 : BitVec 64) (18446744073709551615 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_3_3_7
example (s : riscv_state) : «dfn'SLTU» (7,1,2) (fixture s 3 0 18446744073709551615) =
 (let t := fixture s 3 0 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (0 : BitVec 64) (18446744073709551615 : BitVec 64)], 7) (fixture s 3 0 18446744073709551615) = _
  have numeric : holV2w 64 [BitVec.ult (0 : BitVec 64) (18446744073709551615 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_3_4_0
example (s : riscv_state) : «dfn'SLTU» (0,1,2) (fixture s 3 4294967297 1) =
 (let t := fixture s 3 4294967297 1; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (4294967297 : BitVec 64) (1 : BitVec 64)], 0) (fixture s 3 4294967297 1) = _
  have numeric : holV2w 64 [BitVec.ult (4294967297 : BitVec 64) (1 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_3_4_1
example (s : riscv_state) : «dfn'SLTU» (1,1,2) (fixture s 3 4294967297 1) =
 (let t := fixture s 3 4294967297 1; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (4294967297 : BitVec 64) (1 : BitVec 64)], 1) (fixture s 3 4294967297 1) = _
  have numeric : holV2w 64 [BitVec.ult (4294967297 : BitVec 64) (1 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_3_4_2
example (s : riscv_state) : «dfn'SLTU» (2,1,2) (fixture s 3 4294967297 1) =
 (let t := fixture s 3 4294967297 1; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (4294967297 : BitVec 64) (1 : BitVec 64)], 2) (fixture s 3 4294967297 1) = _
  have numeric : holV2w 64 [BitVec.ult (4294967297 : BitVec 64) (1 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_3_4_7
example (s : riscv_state) : «dfn'SLTU» (7,1,2) (fixture s 3 4294967297 1) =
 (let t := fixture s 3 4294967297 1; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (4294967297 : BitVec 64) (1 : BitVec 64)], 7) (fixture s 3 4294967297 1) = _
  have numeric : holV2w 64 [BitVec.ult (4294967297 : BitVec 64) (1 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_3_5_0
example (s : riscv_state) : «dfn'SLTU» (0,1,2) (fixture s 3 2147483648 1) =
 (let t := fixture s 3 2147483648 1; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (2147483648 : BitVec 64) (1 : BitVec 64)], 0) (fixture s 3 2147483648 1) = _
  have numeric : holV2w 64 [BitVec.ult (2147483648 : BitVec 64) (1 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_3_5_1
example (s : riscv_state) : «dfn'SLTU» (1,1,2) (fixture s 3 2147483648 1) =
 (let t := fixture s 3 2147483648 1; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (2147483648 : BitVec 64) (1 : BitVec 64)], 1) (fixture s 3 2147483648 1) = _
  have numeric : holV2w 64 [BitVec.ult (2147483648 : BitVec 64) (1 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_3_5_2
example (s : riscv_state) : «dfn'SLTU» (2,1,2) (fixture s 3 2147483648 1) =
 (let t := fixture s 3 2147483648 1; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (2147483648 : BitVec 64) (1 : BitVec 64)], 2) (fixture s 3 2147483648 1) = _
  have numeric : holV2w 64 [BitVec.ult (2147483648 : BitVec 64) (1 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_3_5_7
example (s : riscv_state) : «dfn'SLTU» (7,1,2) (fixture s 3 2147483648 1) =
 (let t := fixture s 3 2147483648 1; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (2147483648 : BitVec 64) (1 : BitVec 64)], 7) (fixture s 3 2147483648 1) = _
  have numeric : holV2w 64 [BitVec.ult (2147483648 : BitVec 64) (1 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_3_6_0
example (s : riscv_state) : «dfn'SLTU» (0,1,2) (fixture s 3 9223372036854775808 0) =
 (let t := fixture s 3 9223372036854775808 0; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (9223372036854775808 : BitVec 64) (0 : BitVec 64)], 0) (fixture s 3 9223372036854775808 0) = _
  have numeric : holV2w 64 [BitVec.ult (9223372036854775808 : BitVec 64) (0 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_3_6_1
example (s : riscv_state) : «dfn'SLTU» (1,1,2) (fixture s 3 9223372036854775808 0) =
 (let t := fixture s 3 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (9223372036854775808 : BitVec 64) (0 : BitVec 64)], 1) (fixture s 3 9223372036854775808 0) = _
  have numeric : holV2w 64 [BitVec.ult (9223372036854775808 : BitVec 64) (0 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_3_6_2
example (s : riscv_state) : «dfn'SLTU» (2,1,2) (fixture s 3 9223372036854775808 0) =
 (let t := fixture s 3 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (9223372036854775808 : BitVec 64) (0 : BitVec 64)], 2) (fixture s 3 9223372036854775808 0) = _
  have numeric : holV2w 64 [BitVec.ult (9223372036854775808 : BitVec 64) (0 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_3_6_7
example (s : riscv_state) : «dfn'SLTU» (7,1,2) (fixture s 3 9223372036854775808 0) =
 (let t := fixture s 3 9223372036854775808 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (9223372036854775808 : BitVec 64) (0 : BitVec 64)], 7) (fixture s 3 9223372036854775808 0) = _
  have numeric : holV2w 64 [BitVec.ult (9223372036854775808 : BitVec 64) (0 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_3_7_0
example (s : riscv_state) : «dfn'SLTU» (0,1,2) (fixture s 3 18446744073709551615 18446744073709551615) =
 (let t := fixture s 3 18446744073709551615 18446744073709551615; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (18446744073709551615 : BitVec 64) (18446744073709551615 : BitVec 64)], 0) (fixture s 3 18446744073709551615 18446744073709551615) = _
  have numeric : holV2w 64 [BitVec.ult (18446744073709551615 : BitVec 64) (18446744073709551615 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_3_7_1
example (s : riscv_state) : «dfn'SLTU» (1,1,2) (fixture s 3 18446744073709551615 18446744073709551615) =
 (let t := fixture s 3 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (18446744073709551615 : BitVec 64) (18446744073709551615 : BitVec 64)], 1) (fixture s 3 18446744073709551615 18446744073709551615) = _
  have numeric : holV2w 64 [BitVec.ult (18446744073709551615 : BitVec 64) (18446744073709551615 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_3_7_2
example (s : riscv_state) : «dfn'SLTU» (2,1,2) (fixture s 3 18446744073709551615 18446744073709551615) =
 (let t := fixture s 3 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (18446744073709551615 : BitVec 64) (18446744073709551615 : BitVec 64)], 2) (fixture s 3 18446744073709551615 18446744073709551615) = _
  have numeric : holV2w 64 [BitVec.ult (18446744073709551615 : BitVec 64) (18446744073709551615 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_3_7_7
example (s : riscv_state) : «dfn'SLTU» (7,1,2) (fixture s 3 18446744073709551615 18446744073709551615) =
 (let t := fixture s 3 18446744073709551615 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (18446744073709551615 : BitVec 64) (18446744073709551615 : BitVec 64)], 7) (fixture s 3 18446744073709551615 18446744073709551615) = _
  have numeric : holV2w 64 [BitVec.ult (18446744073709551615 : BitVec 64) (18446744073709551615 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_3_8_0
example (s : riscv_state) : «dfn'SLTU» (0,0,2) (fixture s 3 17 19) =
 (let t := fixture s 3 17 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (0 : BitVec 64) (19 : BitVec 64)], 0) (fixture s 3 17 19) = _
  have numeric : holV2w 64 [BitVec.ult (0 : BitVec 64) (19 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_3_8_1
example (s : riscv_state) : «dfn'SLTU» (1,0,2) (fixture s 3 17 19) =
 (let t := fixture s 3 17 19; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (0 : BitVec 64) (19 : BitVec 64)], 1) (fixture s 3 17 19) = _
  have numeric : holV2w 64 [BitVec.ult (0 : BitVec 64) (19 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_3_8_2
example (s : riscv_state) : «dfn'SLTU» (2,0,2) (fixture s 3 17 19) =
 (let t := fixture s 3 17 19; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (0 : BitVec 64) (19 : BitVec 64)], 2) (fixture s 3 17 19) = _
  have numeric : holV2w 64 [BitVec.ult (0 : BitVec 64) (19 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_3_8_7
example (s : riscv_state) : «dfn'SLTU» (7,0,2) (fixture s 3 17 19) =
 (let t := fixture s 3 17 19; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (0 : BitVec 64) (19 : BitVec 64)], 7) (fixture s 3 17 19) = _
  have numeric : holV2w 64 [BitVec.ult (0 : BitVec 64) (19 : BitVec 64)] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_3_9_0
example (s : riscv_state) : «dfn'SLTU» (0,1,0) (fixture s 3 17 19) =
 (let t := fixture s 3 17 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (17 : BitVec 64) (0 : BitVec 64)], 0) (fixture s 3 17 19) = _
  have numeric : holV2w 64 [BitVec.ult (17 : BitVec 64) (0 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_3_9_1
example (s : riscv_state) : «dfn'SLTU» (1,1,0) (fixture s 3 17 19) =
 (let t := fixture s 3 17 19; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (17 : BitVec 64) (0 : BitVec 64)], 1) (fixture s 3 17 19) = _
  have numeric : holV2w 64 [BitVec.ult (17 : BitVec 64) (0 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_3_9_2
example (s : riscv_state) : «dfn'SLTU» (2,1,0) (fixture s 3 17 19) =
 (let t := fixture s 3 17 19; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (17 : BitVec 64) (0 : BitVec 64)], 2) (fixture s 3 17 19) = _
  have numeric : holV2w 64 [BitVec.ult (17 : BitVec 64) (0 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTU_3_9_7
example (s : riscv_state) : «dfn'SLTU» (7,1,0) (fixture s 3 17 19) =
 (let t := fixture s 3 17 19; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (17 : BitVec 64) (0 : BitVec 64)], 7) (fixture s 3 17 19) = _
  have numeric : holV2w 64 [BitVec.ult (17 : BitVec 64) (0 : BitVec 64)] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_0_0_0
example (s : riscv_state) : «dfn'SLTI» (0,1,0) (fixture s 0 0 19) =
 (let t := fixture s 0 0 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (0 : BitVec 12))], 0) (fixture s 0 0 19) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (0 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_0_0_1
example (s : riscv_state) : «dfn'SLTI» (1,1,0) (fixture s 0 0 19) =
 (let t := fixture s 0 0 19; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (0 : BitVec 12))], 1) (fixture s 0 0 19) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (0 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_0_0_7
example (s : riscv_state) : «dfn'SLTI» (7,1,0) (fixture s 0 0 19) =
 (let t := fixture s 0 0 19; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (0 : BitVec 12))], 7) (fixture s 0 0 19) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (0 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_0_1_0
example (s : riscv_state) : «dfn'SLTI» (0,1,1) (fixture s 0 0 19) =
 (let t := fixture s 0 0 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (1 : BitVec 12))], 0) (fixture s 0 0 19) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (1 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_0_1_1
example (s : riscv_state) : «dfn'SLTI» (1,1,1) (fixture s 0 0 19) =
 (let t := fixture s 0 0 19; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (1 : BitVec 12))], 1) (fixture s 0 0 19) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (1 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_0_1_7
example (s : riscv_state) : «dfn'SLTI» (7,1,1) (fixture s 0 0 19) =
 (let t := fixture s 0 0 19; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (1 : BitVec 12))], 7) (fixture s 0 0 19) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (1 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_0_2_0
example (s : riscv_state) : «dfn'SLTI» (0,1,4095) (fixture s 0 0 19) =
 (let t := fixture s 0 0 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (4095 : BitVec 12))], 0) (fixture s 0 0 19) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (4095 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_0_2_1
example (s : riscv_state) : «dfn'SLTI» (1,1,4095) (fixture s 0 0 19) =
 (let t := fixture s 0 0 19; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (4095 : BitVec 12))], 1) (fixture s 0 0 19) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (4095 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_0_2_7
example (s : riscv_state) : «dfn'SLTI» (7,1,4095) (fixture s 0 0 19) =
 (let t := fixture s 0 0 19; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (4095 : BitVec 12))], 7) (fixture s 0 0 19) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (4095 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_0_3_0
example (s : riscv_state) : «dfn'SLTI» (0,1,4095) (fixture s 0 18446744073709551615 19) =
 (let t := fixture s 0 18446744073709551615 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.signExtend 64 (4095 : BitVec 12))], 0) (fixture s 0 18446744073709551615 19) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.signExtend 64 (4095 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_0_3_1
example (s : riscv_state) : «dfn'SLTI» (1,1,4095) (fixture s 0 18446744073709551615 19) =
 (let t := fixture s 0 18446744073709551615 19; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.signExtend 64 (4095 : BitVec 12))], 1) (fixture s 0 18446744073709551615 19) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.signExtend 64 (4095 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_0_3_7
example (s : riscv_state) : «dfn'SLTI» (7,1,4095) (fixture s 0 18446744073709551615 19) =
 (let t := fixture s 0 18446744073709551615 19; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.signExtend 64 (4095 : BitVec 12))], 7) (fixture s 0 18446744073709551615 19) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.signExtend 64 (4095 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_0_4_0
example (s : riscv_state) : «dfn'SLTI» (0,1,2047) (fixture s 0 2147483647 19) =
 (let t := fixture s 0 2147483647 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483647 : BitVec 64))) (BitVec.signExtend 64 (2047 : BitVec 12))], 0) (fixture s 0 2147483647 19) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483647 : BitVec 64))) (BitVec.signExtend 64 (2047 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_0_4_1
example (s : riscv_state) : «dfn'SLTI» (1,1,2047) (fixture s 0 2147483647 19) =
 (let t := fixture s 0 2147483647 19; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483647 : BitVec 64))) (BitVec.signExtend 64 (2047 : BitVec 12))], 1) (fixture s 0 2147483647 19) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483647 : BitVec 64))) (BitVec.signExtend 64 (2047 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_0_4_7
example (s : riscv_state) : «dfn'SLTI» (7,1,2047) (fixture s 0 2147483647 19) =
 (let t := fixture s 0 2147483647 19; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483647 : BitVec 64))) (BitVec.signExtend 64 (2047 : BitVec 12))], 7) (fixture s 0 2147483647 19) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483647 : BitVec 64))) (BitVec.signExtend 64 (2047 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_0_5_0
example (s : riscv_state) : «dfn'SLTI» (0,1,2048) (fixture s 0 2147483648 19) =
 (let t := fixture s 0 2147483648 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) (BitVec.signExtend 64 (2048 : BitVec 12))], 0) (fixture s 0 2147483648 19) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) (BitVec.signExtend 64 (2048 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_0_5_1
example (s : riscv_state) : «dfn'SLTI» (1,1,2048) (fixture s 0 2147483648 19) =
 (let t := fixture s 0 2147483648 19; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) (BitVec.signExtend 64 (2048 : BitVec 12))], 1) (fixture s 0 2147483648 19) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) (BitVec.signExtend 64 (2048 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_0_5_7
example (s : riscv_state) : «dfn'SLTI» (7,1,2048) (fixture s 0 2147483648 19) =
 (let t := fixture s 0 2147483648 19; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) (BitVec.signExtend 64 (2048 : BitVec 12))], 7) (fixture s 0 2147483648 19) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) (BitVec.signExtend 64 (2048 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_0_6_0
example (s : riscv_state) : «dfn'SLTI» (0,1,4095) (fixture s 0 4294967295 19) =
 (let t := fixture s 0 4294967295 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967295 : BitVec 64))) (BitVec.signExtend 64 (4095 : BitVec 12))], 0) (fixture s 0 4294967295 19) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967295 : BitVec 64))) (BitVec.signExtend 64 (4095 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_0_6_1
example (s : riscv_state) : «dfn'SLTI» (1,1,4095) (fixture s 0 4294967295 19) =
 (let t := fixture s 0 4294967295 19; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967295 : BitVec 64))) (BitVec.signExtend 64 (4095 : BitVec 12))], 1) (fixture s 0 4294967295 19) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967295 : BitVec 64))) (BitVec.signExtend 64 (4095 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_0_6_7
example (s : riscv_state) : «dfn'SLTI» (7,1,4095) (fixture s 0 4294967295 19) =
 (let t := fixture s 0 4294967295 19; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967295 : BitVec 64))) (BitVec.signExtend 64 (4095 : BitVec 12))], 7) (fixture s 0 4294967295 19) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967295 : BitVec 64))) (BitVec.signExtend 64 (4095 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_0_7_0
example (s : riscv_state) : «dfn'SLTI» (0,1,1) (fixture s 0 4294967297 19) =
 (let t := fixture s 0 4294967297 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) (BitVec.signExtend 64 (1 : BitVec 12))], 0) (fixture s 0 4294967297 19) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) (BitVec.signExtend 64 (1 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_0_7_1
example (s : riscv_state) : «dfn'SLTI» (1,1,1) (fixture s 0 4294967297 19) =
 (let t := fixture s 0 4294967297 19; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) (BitVec.signExtend 64 (1 : BitVec 12))], 1) (fixture s 0 4294967297 19) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) (BitVec.signExtend 64 (1 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_0_7_7
example (s : riscv_state) : «dfn'SLTI» (7,1,1) (fixture s 0 4294967297 19) =
 (let t := fixture s 0 4294967297 19; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) (BitVec.signExtend 64 (1 : BitVec 12))], 7) (fixture s 0 4294967297 19) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) (BitVec.signExtend 64 (1 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_0_8_0
example (s : riscv_state) : «dfn'SLTI» (0,0,2048) (fixture s 0 17 19) =
 (let t := fixture s 0 17 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (2048 : BitVec 12))], 0) (fixture s 0 17 19) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (2048 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_0_8_1
example (s : riscv_state) : «dfn'SLTI» (1,0,2048) (fixture s 0 17 19) =
 (let t := fixture s 0 17 19; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (2048 : BitVec 12))], 1) (fixture s 0 17 19) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (2048 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_0_8_7
example (s : riscv_state) : «dfn'SLTI» (7,0,2048) (fixture s 0 17 19) =
 (let t := fixture s 0 17 19; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (2048 : BitVec 12))], 7) (fixture s 0 17 19) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (2048 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_0_9_0
example (s : riscv_state) : «dfn'SLTI» (0,1,0) (fixture s 0 9223372036854775808 19) =
 (let t := fixture s 0 9223372036854775808 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.signExtend 64 (0 : BitVec 12))], 0) (fixture s 0 9223372036854775808 19) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.signExtend 64 (0 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_0_9_1
example (s : riscv_state) : «dfn'SLTI» (1,1,0) (fixture s 0 9223372036854775808 19) =
 (let t := fixture s 0 9223372036854775808 19; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.signExtend 64 (0 : BitVec 12))], 1) (fixture s 0 9223372036854775808 19) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.signExtend 64 (0 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_0_9_7
example (s : riscv_state) : «dfn'SLTI» (7,1,0) (fixture s 0 9223372036854775808 19) =
 (let t := fixture s 0 9223372036854775808 19; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.signExtend 64 (0 : BitVec 12))], 7) (fixture s 0 9223372036854775808 19) = _
  have numeric : holV2w 64 [BitVec.slt (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.signExtend 64 (0 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_2_0_0
example (s : riscv_state) : «dfn'SLTI» (0,1,0) (fixture s 2 0 19) =
 (let t := fixture s 2 0 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (0 : BitVec 64) (BitVec.signExtend 64 (0 : BitVec 12))], 0) (fixture s 2 0 19) = _
  have numeric : holV2w 64 [BitVec.slt (0 : BitVec 64) (BitVec.signExtend 64 (0 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_2_0_1
example (s : riscv_state) : «dfn'SLTI» (1,1,0) (fixture s 2 0 19) =
 (let t := fixture s 2 0 19; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (0 : BitVec 64) (BitVec.signExtend 64 (0 : BitVec 12))], 1) (fixture s 2 0 19) = _
  have numeric : holV2w 64 [BitVec.slt (0 : BitVec 64) (BitVec.signExtend 64 (0 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_2_0_7
example (s : riscv_state) : «dfn'SLTI» (7,1,0) (fixture s 2 0 19) =
 (let t := fixture s 2 0 19; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (0 : BitVec 64) (BitVec.signExtend 64 (0 : BitVec 12))], 7) (fixture s 2 0 19) = _
  have numeric : holV2w 64 [BitVec.slt (0 : BitVec 64) (BitVec.signExtend 64 (0 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_2_1_0
example (s : riscv_state) : «dfn'SLTI» (0,1,1) (fixture s 2 0 19) =
 (let t := fixture s 2 0 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (0 : BitVec 64) (BitVec.signExtend 64 (1 : BitVec 12))], 0) (fixture s 2 0 19) = _
  have numeric : holV2w 64 [BitVec.slt (0 : BitVec 64) (BitVec.signExtend 64 (1 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_2_1_1
example (s : riscv_state) : «dfn'SLTI» (1,1,1) (fixture s 2 0 19) =
 (let t := fixture s 2 0 19; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (0 : BitVec 64) (BitVec.signExtend 64 (1 : BitVec 12))], 1) (fixture s 2 0 19) = _
  have numeric : holV2w 64 [BitVec.slt (0 : BitVec 64) (BitVec.signExtend 64 (1 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_2_1_7
example (s : riscv_state) : «dfn'SLTI» (7,1,1) (fixture s 2 0 19) =
 (let t := fixture s 2 0 19; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (0 : BitVec 64) (BitVec.signExtend 64 (1 : BitVec 12))], 7) (fixture s 2 0 19) = _
  have numeric : holV2w 64 [BitVec.slt (0 : BitVec 64) (BitVec.signExtend 64 (1 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_2_2_0
example (s : riscv_state) : «dfn'SLTI» (0,1,4095) (fixture s 2 0 19) =
 (let t := fixture s 2 0 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (0 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))], 0) (fixture s 2 0 19) = _
  have numeric : holV2w 64 [BitVec.slt (0 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_2_2_1
example (s : riscv_state) : «dfn'SLTI» (1,1,4095) (fixture s 2 0 19) =
 (let t := fixture s 2 0 19; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (0 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))], 1) (fixture s 2 0 19) = _
  have numeric : holV2w 64 [BitVec.slt (0 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_2_2_7
example (s : riscv_state) : «dfn'SLTI» (7,1,4095) (fixture s 2 0 19) =
 (let t := fixture s 2 0 19; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (0 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))], 7) (fixture s 2 0 19) = _
  have numeric : holV2w 64 [BitVec.slt (0 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_2_3_0
example (s : riscv_state) : «dfn'SLTI» (0,1,4095) (fixture s 2 18446744073709551615 19) =
 (let t := fixture s 2 18446744073709551615 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (18446744073709551615 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))], 0) (fixture s 2 18446744073709551615 19) = _
  have numeric : holV2w 64 [BitVec.slt (18446744073709551615 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_2_3_1
example (s : riscv_state) : «dfn'SLTI» (1,1,4095) (fixture s 2 18446744073709551615 19) =
 (let t := fixture s 2 18446744073709551615 19; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (18446744073709551615 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))], 1) (fixture s 2 18446744073709551615 19) = _
  have numeric : holV2w 64 [BitVec.slt (18446744073709551615 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_2_3_7
example (s : riscv_state) : «dfn'SLTI» (7,1,4095) (fixture s 2 18446744073709551615 19) =
 (let t := fixture s 2 18446744073709551615 19; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (18446744073709551615 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))], 7) (fixture s 2 18446744073709551615 19) = _
  have numeric : holV2w 64 [BitVec.slt (18446744073709551615 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_2_4_0
example (s : riscv_state) : «dfn'SLTI» (0,1,2047) (fixture s 2 2147483647 19) =
 (let t := fixture s 2 2147483647 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (2147483647 : BitVec 64) (BitVec.signExtend 64 (2047 : BitVec 12))], 0) (fixture s 2 2147483647 19) = _
  have numeric : holV2w 64 [BitVec.slt (2147483647 : BitVec 64) (BitVec.signExtend 64 (2047 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_2_4_1
example (s : riscv_state) : «dfn'SLTI» (1,1,2047) (fixture s 2 2147483647 19) =
 (let t := fixture s 2 2147483647 19; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (2147483647 : BitVec 64) (BitVec.signExtend 64 (2047 : BitVec 12))], 1) (fixture s 2 2147483647 19) = _
  have numeric : holV2w 64 [BitVec.slt (2147483647 : BitVec 64) (BitVec.signExtend 64 (2047 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_2_4_7
example (s : riscv_state) : «dfn'SLTI» (7,1,2047) (fixture s 2 2147483647 19) =
 (let t := fixture s 2 2147483647 19; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (2147483647 : BitVec 64) (BitVec.signExtend 64 (2047 : BitVec 12))], 7) (fixture s 2 2147483647 19) = _
  have numeric : holV2w 64 [BitVec.slt (2147483647 : BitVec 64) (BitVec.signExtend 64 (2047 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_2_5_0
example (s : riscv_state) : «dfn'SLTI» (0,1,2048) (fixture s 2 2147483648 19) =
 (let t := fixture s 2 2147483648 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (2147483648 : BitVec 64) (BitVec.signExtend 64 (2048 : BitVec 12))], 0) (fixture s 2 2147483648 19) = _
  have numeric : holV2w 64 [BitVec.slt (2147483648 : BitVec 64) (BitVec.signExtend 64 (2048 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_2_5_1
example (s : riscv_state) : «dfn'SLTI» (1,1,2048) (fixture s 2 2147483648 19) =
 (let t := fixture s 2 2147483648 19; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (2147483648 : BitVec 64) (BitVec.signExtend 64 (2048 : BitVec 12))], 1) (fixture s 2 2147483648 19) = _
  have numeric : holV2w 64 [BitVec.slt (2147483648 : BitVec 64) (BitVec.signExtend 64 (2048 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_2_5_7
example (s : riscv_state) : «dfn'SLTI» (7,1,2048) (fixture s 2 2147483648 19) =
 (let t := fixture s 2 2147483648 19; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (2147483648 : BitVec 64) (BitVec.signExtend 64 (2048 : BitVec 12))], 7) (fixture s 2 2147483648 19) = _
  have numeric : holV2w 64 [BitVec.slt (2147483648 : BitVec 64) (BitVec.signExtend 64 (2048 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_2_6_0
example (s : riscv_state) : «dfn'SLTI» (0,1,4095) (fixture s 2 4294967295 19) =
 (let t := fixture s 2 4294967295 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (4294967295 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))], 0) (fixture s 2 4294967295 19) = _
  have numeric : holV2w 64 [BitVec.slt (4294967295 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_2_6_1
example (s : riscv_state) : «dfn'SLTI» (1,1,4095) (fixture s 2 4294967295 19) =
 (let t := fixture s 2 4294967295 19; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (4294967295 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))], 1) (fixture s 2 4294967295 19) = _
  have numeric : holV2w 64 [BitVec.slt (4294967295 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_2_6_7
example (s : riscv_state) : «dfn'SLTI» (7,1,4095) (fixture s 2 4294967295 19) =
 (let t := fixture s 2 4294967295 19; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (4294967295 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))], 7) (fixture s 2 4294967295 19) = _
  have numeric : holV2w 64 [BitVec.slt (4294967295 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_2_7_0
example (s : riscv_state) : «dfn'SLTI» (0,1,1) (fixture s 2 4294967297 19) =
 (let t := fixture s 2 4294967297 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (4294967297 : BitVec 64) (BitVec.signExtend 64 (1 : BitVec 12))], 0) (fixture s 2 4294967297 19) = _
  have numeric : holV2w 64 [BitVec.slt (4294967297 : BitVec 64) (BitVec.signExtend 64 (1 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_2_7_1
example (s : riscv_state) : «dfn'SLTI» (1,1,1) (fixture s 2 4294967297 19) =
 (let t := fixture s 2 4294967297 19; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (4294967297 : BitVec 64) (BitVec.signExtend 64 (1 : BitVec 12))], 1) (fixture s 2 4294967297 19) = _
  have numeric : holV2w 64 [BitVec.slt (4294967297 : BitVec 64) (BitVec.signExtend 64 (1 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_2_7_7
example (s : riscv_state) : «dfn'SLTI» (7,1,1) (fixture s 2 4294967297 19) =
 (let t := fixture s 2 4294967297 19; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (4294967297 : BitVec 64) (BitVec.signExtend 64 (1 : BitVec 12))], 7) (fixture s 2 4294967297 19) = _
  have numeric : holV2w 64 [BitVec.slt (4294967297 : BitVec 64) (BitVec.signExtend 64 (1 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_2_8_0
example (s : riscv_state) : «dfn'SLTI» (0,0,2048) (fixture s 2 17 19) =
 (let t := fixture s 2 17 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (0 : BitVec 64) (BitVec.signExtend 64 (2048 : BitVec 12))], 0) (fixture s 2 17 19) = _
  have numeric : holV2w 64 [BitVec.slt (0 : BitVec 64) (BitVec.signExtend 64 (2048 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_2_8_1
example (s : riscv_state) : «dfn'SLTI» (1,0,2048) (fixture s 2 17 19) =
 (let t := fixture s 2 17 19; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (0 : BitVec 64) (BitVec.signExtend 64 (2048 : BitVec 12))], 1) (fixture s 2 17 19) = _
  have numeric : holV2w 64 [BitVec.slt (0 : BitVec 64) (BitVec.signExtend 64 (2048 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_2_8_7
example (s : riscv_state) : «dfn'SLTI» (7,0,2048) (fixture s 2 17 19) =
 (let t := fixture s 2 17 19; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (0 : BitVec 64) (BitVec.signExtend 64 (2048 : BitVec 12))], 7) (fixture s 2 17 19) = _
  have numeric : holV2w 64 [BitVec.slt (0 : BitVec 64) (BitVec.signExtend 64 (2048 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_2_9_0
example (s : riscv_state) : «dfn'SLTI» (0,1,0) (fixture s 2 9223372036854775808 19) =
 (let t := fixture s 2 9223372036854775808 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (9223372036854775808 : BitVec 64) (BitVec.signExtend 64 (0 : BitVec 12))], 0) (fixture s 2 9223372036854775808 19) = _
  have numeric : holV2w 64 [BitVec.slt (9223372036854775808 : BitVec 64) (BitVec.signExtend 64 (0 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_2_9_1
example (s : riscv_state) : «dfn'SLTI» (1,1,0) (fixture s 2 9223372036854775808 19) =
 (let t := fixture s 2 9223372036854775808 19; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (9223372036854775808 : BitVec 64) (BitVec.signExtend 64 (0 : BitVec 12))], 1) (fixture s 2 9223372036854775808 19) = _
  have numeric : holV2w 64 [BitVec.slt (9223372036854775808 : BitVec 64) (BitVec.signExtend 64 (0 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_2_9_7
example (s : riscv_state) : «dfn'SLTI» (7,1,0) (fixture s 2 9223372036854775808 19) =
 (let t := fixture s 2 9223372036854775808 19; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (9223372036854775808 : BitVec 64) (BitVec.signExtend 64 (0 : BitVec 12))], 7) (fixture s 2 9223372036854775808 19) = _
  have numeric : holV2w 64 [BitVec.slt (9223372036854775808 : BitVec 64) (BitVec.signExtend 64 (0 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_3_0_0
example (s : riscv_state) : «dfn'SLTI» (0,1,0) (fixture s 3 0 19) =
 (let t := fixture s 3 0 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (0 : BitVec 64) (BitVec.signExtend 64 (0 : BitVec 12))], 0) (fixture s 3 0 19) = _
  have numeric : holV2w 64 [BitVec.slt (0 : BitVec 64) (BitVec.signExtend 64 (0 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_3_0_1
example (s : riscv_state) : «dfn'SLTI» (1,1,0) (fixture s 3 0 19) =
 (let t := fixture s 3 0 19; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (0 : BitVec 64) (BitVec.signExtend 64 (0 : BitVec 12))], 1) (fixture s 3 0 19) = _
  have numeric : holV2w 64 [BitVec.slt (0 : BitVec 64) (BitVec.signExtend 64 (0 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_3_0_7
example (s : riscv_state) : «dfn'SLTI» (7,1,0) (fixture s 3 0 19) =
 (let t := fixture s 3 0 19; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (0 : BitVec 64) (BitVec.signExtend 64 (0 : BitVec 12))], 7) (fixture s 3 0 19) = _
  have numeric : holV2w 64 [BitVec.slt (0 : BitVec 64) (BitVec.signExtend 64 (0 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_3_1_0
example (s : riscv_state) : «dfn'SLTI» (0,1,1) (fixture s 3 0 19) =
 (let t := fixture s 3 0 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (0 : BitVec 64) (BitVec.signExtend 64 (1 : BitVec 12))], 0) (fixture s 3 0 19) = _
  have numeric : holV2w 64 [BitVec.slt (0 : BitVec 64) (BitVec.signExtend 64 (1 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_3_1_1
example (s : riscv_state) : «dfn'SLTI» (1,1,1) (fixture s 3 0 19) =
 (let t := fixture s 3 0 19; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (0 : BitVec 64) (BitVec.signExtend 64 (1 : BitVec 12))], 1) (fixture s 3 0 19) = _
  have numeric : holV2w 64 [BitVec.slt (0 : BitVec 64) (BitVec.signExtend 64 (1 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_3_1_7
example (s : riscv_state) : «dfn'SLTI» (7,1,1) (fixture s 3 0 19) =
 (let t := fixture s 3 0 19; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (0 : BitVec 64) (BitVec.signExtend 64 (1 : BitVec 12))], 7) (fixture s 3 0 19) = _
  have numeric : holV2w 64 [BitVec.slt (0 : BitVec 64) (BitVec.signExtend 64 (1 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_3_2_0
example (s : riscv_state) : «dfn'SLTI» (0,1,4095) (fixture s 3 0 19) =
 (let t := fixture s 3 0 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (0 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))], 0) (fixture s 3 0 19) = _
  have numeric : holV2w 64 [BitVec.slt (0 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_3_2_1
example (s : riscv_state) : «dfn'SLTI» (1,1,4095) (fixture s 3 0 19) =
 (let t := fixture s 3 0 19; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (0 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))], 1) (fixture s 3 0 19) = _
  have numeric : holV2w 64 [BitVec.slt (0 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_3_2_7
example (s : riscv_state) : «dfn'SLTI» (7,1,4095) (fixture s 3 0 19) =
 (let t := fixture s 3 0 19; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (0 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))], 7) (fixture s 3 0 19) = _
  have numeric : holV2w 64 [BitVec.slt (0 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_3_3_0
example (s : riscv_state) : «dfn'SLTI» (0,1,4095) (fixture s 3 18446744073709551615 19) =
 (let t := fixture s 3 18446744073709551615 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (18446744073709551615 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))], 0) (fixture s 3 18446744073709551615 19) = _
  have numeric : holV2w 64 [BitVec.slt (18446744073709551615 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_3_3_1
example (s : riscv_state) : «dfn'SLTI» (1,1,4095) (fixture s 3 18446744073709551615 19) =
 (let t := fixture s 3 18446744073709551615 19; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (18446744073709551615 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))], 1) (fixture s 3 18446744073709551615 19) = _
  have numeric : holV2w 64 [BitVec.slt (18446744073709551615 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_3_3_7
example (s : riscv_state) : «dfn'SLTI» (7,1,4095) (fixture s 3 18446744073709551615 19) =
 (let t := fixture s 3 18446744073709551615 19; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (18446744073709551615 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))], 7) (fixture s 3 18446744073709551615 19) = _
  have numeric : holV2w 64 [BitVec.slt (18446744073709551615 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_3_4_0
example (s : riscv_state) : «dfn'SLTI» (0,1,2047) (fixture s 3 2147483647 19) =
 (let t := fixture s 3 2147483647 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (2147483647 : BitVec 64) (BitVec.signExtend 64 (2047 : BitVec 12))], 0) (fixture s 3 2147483647 19) = _
  have numeric : holV2w 64 [BitVec.slt (2147483647 : BitVec 64) (BitVec.signExtend 64 (2047 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_3_4_1
example (s : riscv_state) : «dfn'SLTI» (1,1,2047) (fixture s 3 2147483647 19) =
 (let t := fixture s 3 2147483647 19; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (2147483647 : BitVec 64) (BitVec.signExtend 64 (2047 : BitVec 12))], 1) (fixture s 3 2147483647 19) = _
  have numeric : holV2w 64 [BitVec.slt (2147483647 : BitVec 64) (BitVec.signExtend 64 (2047 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_3_4_7
example (s : riscv_state) : «dfn'SLTI» (7,1,2047) (fixture s 3 2147483647 19) =
 (let t := fixture s 3 2147483647 19; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (2147483647 : BitVec 64) (BitVec.signExtend 64 (2047 : BitVec 12))], 7) (fixture s 3 2147483647 19) = _
  have numeric : holV2w 64 [BitVec.slt (2147483647 : BitVec 64) (BitVec.signExtend 64 (2047 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_3_5_0
example (s : riscv_state) : «dfn'SLTI» (0,1,2048) (fixture s 3 2147483648 19) =
 (let t := fixture s 3 2147483648 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (2147483648 : BitVec 64) (BitVec.signExtend 64 (2048 : BitVec 12))], 0) (fixture s 3 2147483648 19) = _
  have numeric : holV2w 64 [BitVec.slt (2147483648 : BitVec 64) (BitVec.signExtend 64 (2048 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_3_5_1
example (s : riscv_state) : «dfn'SLTI» (1,1,2048) (fixture s 3 2147483648 19) =
 (let t := fixture s 3 2147483648 19; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (2147483648 : BitVec 64) (BitVec.signExtend 64 (2048 : BitVec 12))], 1) (fixture s 3 2147483648 19) = _
  have numeric : holV2w 64 [BitVec.slt (2147483648 : BitVec 64) (BitVec.signExtend 64 (2048 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_3_5_7
example (s : riscv_state) : «dfn'SLTI» (7,1,2048) (fixture s 3 2147483648 19) =
 (let t := fixture s 3 2147483648 19; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (2147483648 : BitVec 64) (BitVec.signExtend 64 (2048 : BitVec 12))], 7) (fixture s 3 2147483648 19) = _
  have numeric : holV2w 64 [BitVec.slt (2147483648 : BitVec 64) (BitVec.signExtend 64 (2048 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_3_6_0
example (s : riscv_state) : «dfn'SLTI» (0,1,4095) (fixture s 3 4294967295 19) =
 (let t := fixture s 3 4294967295 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (4294967295 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))], 0) (fixture s 3 4294967295 19) = _
  have numeric : holV2w 64 [BitVec.slt (4294967295 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_3_6_1
example (s : riscv_state) : «dfn'SLTI» (1,1,4095) (fixture s 3 4294967295 19) =
 (let t := fixture s 3 4294967295 19; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (4294967295 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))], 1) (fixture s 3 4294967295 19) = _
  have numeric : holV2w 64 [BitVec.slt (4294967295 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_3_6_7
example (s : riscv_state) : «dfn'SLTI» (7,1,4095) (fixture s 3 4294967295 19) =
 (let t := fixture s 3 4294967295 19; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (4294967295 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))], 7) (fixture s 3 4294967295 19) = _
  have numeric : holV2w 64 [BitVec.slt (4294967295 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_3_7_0
example (s : riscv_state) : «dfn'SLTI» (0,1,1) (fixture s 3 4294967297 19) =
 (let t := fixture s 3 4294967297 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (4294967297 : BitVec 64) (BitVec.signExtend 64 (1 : BitVec 12))], 0) (fixture s 3 4294967297 19) = _
  have numeric : holV2w 64 [BitVec.slt (4294967297 : BitVec 64) (BitVec.signExtend 64 (1 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_3_7_1
example (s : riscv_state) : «dfn'SLTI» (1,1,1) (fixture s 3 4294967297 19) =
 (let t := fixture s 3 4294967297 19; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (4294967297 : BitVec 64) (BitVec.signExtend 64 (1 : BitVec 12))], 1) (fixture s 3 4294967297 19) = _
  have numeric : holV2w 64 [BitVec.slt (4294967297 : BitVec 64) (BitVec.signExtend 64 (1 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_3_7_7
example (s : riscv_state) : «dfn'SLTI» (7,1,1) (fixture s 3 4294967297 19) =
 (let t := fixture s 3 4294967297 19; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (4294967297 : BitVec 64) (BitVec.signExtend 64 (1 : BitVec 12))], 7) (fixture s 3 4294967297 19) = _
  have numeric : holV2w 64 [BitVec.slt (4294967297 : BitVec 64) (BitVec.signExtend 64 (1 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_3_8_0
example (s : riscv_state) : «dfn'SLTI» (0,0,2048) (fixture s 3 17 19) =
 (let t := fixture s 3 17 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (0 : BitVec 64) (BitVec.signExtend 64 (2048 : BitVec 12))], 0) (fixture s 3 17 19) = _
  have numeric : holV2w 64 [BitVec.slt (0 : BitVec 64) (BitVec.signExtend 64 (2048 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_3_8_1
example (s : riscv_state) : «dfn'SLTI» (1,0,2048) (fixture s 3 17 19) =
 (let t := fixture s 3 17 19; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (0 : BitVec 64) (BitVec.signExtend 64 (2048 : BitVec 12))], 1) (fixture s 3 17 19) = _
  have numeric : holV2w 64 [BitVec.slt (0 : BitVec 64) (BitVec.signExtend 64 (2048 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_3_8_7
example (s : riscv_state) : «dfn'SLTI» (7,0,2048) (fixture s 3 17 19) =
 (let t := fixture s 3 17 19; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (0 : BitVec 64) (BitVec.signExtend 64 (2048 : BitVec 12))], 7) (fixture s 3 17 19) = _
  have numeric : holV2w 64 [BitVec.slt (0 : BitVec 64) (BitVec.signExtend 64 (2048 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_3_9_0
example (s : riscv_state) : «dfn'SLTI» (0,1,0) (fixture s 3 9223372036854775808 19) =
 (let t := fixture s 3 9223372036854775808 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (9223372036854775808 : BitVec 64) (BitVec.signExtend 64 (0 : BitVec 12))], 0) (fixture s 3 9223372036854775808 19) = _
  have numeric : holV2w 64 [BitVec.slt (9223372036854775808 : BitVec 64) (BitVec.signExtend 64 (0 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_3_9_1
example (s : riscv_state) : «dfn'SLTI» (1,1,0) (fixture s 3 9223372036854775808 19) =
 (let t := fixture s 3 9223372036854775808 19; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (9223372036854775808 : BitVec 64) (BitVec.signExtend 64 (0 : BitVec 12))], 1) (fixture s 3 9223372036854775808 19) = _
  have numeric : holV2w 64 [BitVec.slt (9223372036854775808 : BitVec 64) (BitVec.signExtend 64 (0 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTI_3_9_7
example (s : riscv_state) : «dfn'SLTI» (7,1,0) (fixture s 3 9223372036854775808 19) =
 (let t := fixture s 3 9223372036854775808 19; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.slt (9223372036854775808 : BitVec 64) (BitVec.signExtend 64 (0 : BitVec 12))], 7) (fixture s 3 9223372036854775808 19) = _
  have numeric : holV2w 64 [BitVec.slt (9223372036854775808 : BitVec 64) (BitVec.signExtend 64 (0 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_0_0_0
example (s : riscv_state) : «dfn'SLTIU» (0,1,0) (fixture s 0 0 19) =
 (let t := fixture s 0 0 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (0 : BitVec 12))], 0) (fixture s 0 0 19) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (0 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_0_0_1
example (s : riscv_state) : «dfn'SLTIU» (1,1,0) (fixture s 0 0 19) =
 (let t := fixture s 0 0 19; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (0 : BitVec 12))], 1) (fixture s 0 0 19) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (0 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_0_0_7
example (s : riscv_state) : «dfn'SLTIU» (7,1,0) (fixture s 0 0 19) =
 (let t := fixture s 0 0 19; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (0 : BitVec 12))], 7) (fixture s 0 0 19) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (0 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_0_1_0
example (s : riscv_state) : «dfn'SLTIU» (0,1,1) (fixture s 0 0 19) =
 (let t := fixture s 0 0 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (1 : BitVec 12))], 0) (fixture s 0 0 19) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (1 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_0_1_1
example (s : riscv_state) : «dfn'SLTIU» (1,1,1) (fixture s 0 0 19) =
 (let t := fixture s 0 0 19; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (1 : BitVec 12))], 1) (fixture s 0 0 19) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (1 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_0_1_7
example (s : riscv_state) : «dfn'SLTIU» (7,1,1) (fixture s 0 0 19) =
 (let t := fixture s 0 0 19; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (1 : BitVec 12))], 7) (fixture s 0 0 19) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (1 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_0_2_0
example (s : riscv_state) : «dfn'SLTIU» (0,1,4095) (fixture s 0 0 19) =
 (let t := fixture s 0 0 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (4095 : BitVec 12))], 0) (fixture s 0 0 19) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (4095 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_0_2_1
example (s : riscv_state) : «dfn'SLTIU» (1,1,4095) (fixture s 0 0 19) =
 (let t := fixture s 0 0 19; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (4095 : BitVec 12))], 1) (fixture s 0 0 19) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (4095 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_0_2_7
example (s : riscv_state) : «dfn'SLTIU» (7,1,4095) (fixture s 0 0 19) =
 (let t := fixture s 0 0 19; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (4095 : BitVec 12))], 7) (fixture s 0 0 19) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (4095 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_0_3_0
example (s : riscv_state) : «dfn'SLTIU» (0,1,4095) (fixture s 0 18446744073709551615 19) =
 (let t := fixture s 0 18446744073709551615 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.signExtend 64 (4095 : BitVec 12))], 0) (fixture s 0 18446744073709551615 19) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.signExtend 64 (4095 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_0_3_1
example (s : riscv_state) : «dfn'SLTIU» (1,1,4095) (fixture s 0 18446744073709551615 19) =
 (let t := fixture s 0 18446744073709551615 19; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.signExtend 64 (4095 : BitVec 12))], 1) (fixture s 0 18446744073709551615 19) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.signExtend 64 (4095 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_0_3_7
example (s : riscv_state) : «dfn'SLTIU» (7,1,4095) (fixture s 0 18446744073709551615 19) =
 (let t := fixture s 0 18446744073709551615 19; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.signExtend 64 (4095 : BitVec 12))], 7) (fixture s 0 18446744073709551615 19) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.signExtend 64 (4095 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_0_4_0
example (s : riscv_state) : «dfn'SLTIU» (0,1,2047) (fixture s 0 2147483647 19) =
 (let t := fixture s 0 2147483647 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483647 : BitVec 64))) (BitVec.signExtend 64 (2047 : BitVec 12))], 0) (fixture s 0 2147483647 19) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483647 : BitVec 64))) (BitVec.signExtend 64 (2047 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_0_4_1
example (s : riscv_state) : «dfn'SLTIU» (1,1,2047) (fixture s 0 2147483647 19) =
 (let t := fixture s 0 2147483647 19; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483647 : BitVec 64))) (BitVec.signExtend 64 (2047 : BitVec 12))], 1) (fixture s 0 2147483647 19) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483647 : BitVec 64))) (BitVec.signExtend 64 (2047 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_0_4_7
example (s : riscv_state) : «dfn'SLTIU» (7,1,2047) (fixture s 0 2147483647 19) =
 (let t := fixture s 0 2147483647 19; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483647 : BitVec 64))) (BitVec.signExtend 64 (2047 : BitVec 12))], 7) (fixture s 0 2147483647 19) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483647 : BitVec 64))) (BitVec.signExtend 64 (2047 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_0_5_0
example (s : riscv_state) : «dfn'SLTIU» (0,1,2048) (fixture s 0 2147483648 19) =
 (let t := fixture s 0 2147483648 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) (BitVec.signExtend 64 (2048 : BitVec 12))], 0) (fixture s 0 2147483648 19) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) (BitVec.signExtend 64 (2048 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_0_5_1
example (s : riscv_state) : «dfn'SLTIU» (1,1,2048) (fixture s 0 2147483648 19) =
 (let t := fixture s 0 2147483648 19; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) (BitVec.signExtend 64 (2048 : BitVec 12))], 1) (fixture s 0 2147483648 19) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) (BitVec.signExtend 64 (2048 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_0_5_7
example (s : riscv_state) : «dfn'SLTIU» (7,1,2048) (fixture s 0 2147483648 19) =
 (let t := fixture s 0 2147483648 19; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) (BitVec.signExtend 64 (2048 : BitVec 12))], 7) (fixture s 0 2147483648 19) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) (BitVec.signExtend 64 (2048 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_0_6_0
example (s : riscv_state) : «dfn'SLTIU» (0,1,4095) (fixture s 0 4294967295 19) =
 (let t := fixture s 0 4294967295 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967295 : BitVec 64))) (BitVec.signExtend 64 (4095 : BitVec 12))], 0) (fixture s 0 4294967295 19) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967295 : BitVec 64))) (BitVec.signExtend 64 (4095 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_0_6_1
example (s : riscv_state) : «dfn'SLTIU» (1,1,4095) (fixture s 0 4294967295 19) =
 (let t := fixture s 0 4294967295 19; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967295 : BitVec 64))) (BitVec.signExtend 64 (4095 : BitVec 12))], 1) (fixture s 0 4294967295 19) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967295 : BitVec 64))) (BitVec.signExtend 64 (4095 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_0_6_7
example (s : riscv_state) : «dfn'SLTIU» (7,1,4095) (fixture s 0 4294967295 19) =
 (let t := fixture s 0 4294967295 19; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967295 : BitVec 64))) (BitVec.signExtend 64 (4095 : BitVec 12))], 7) (fixture s 0 4294967295 19) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967295 : BitVec 64))) (BitVec.signExtend 64 (4095 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_0_7_0
example (s : riscv_state) : «dfn'SLTIU» (0,1,1) (fixture s 0 4294967297 19) =
 (let t := fixture s 0 4294967297 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) (BitVec.signExtend 64 (1 : BitVec 12))], 0) (fixture s 0 4294967297 19) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) (BitVec.signExtend 64 (1 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_0_7_1
example (s : riscv_state) : «dfn'SLTIU» (1,1,1) (fixture s 0 4294967297 19) =
 (let t := fixture s 0 4294967297 19; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) (BitVec.signExtend 64 (1 : BitVec 12))], 1) (fixture s 0 4294967297 19) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) (BitVec.signExtend 64 (1 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_0_7_7
example (s : riscv_state) : «dfn'SLTIU» (7,1,1) (fixture s 0 4294967297 19) =
 (let t := fixture s 0 4294967297 19; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) (BitVec.signExtend 64 (1 : BitVec 12))], 7) (fixture s 0 4294967297 19) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (4294967297 : BitVec 64))) (BitVec.signExtend 64 (1 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_0_8_0
example (s : riscv_state) : «dfn'SLTIU» (0,0,2048) (fixture s 0 17 19) =
 (let t := fixture s 0 17 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (2048 : BitVec 12))], 0) (fixture s 0 17 19) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (2048 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_0_8_1
example (s : riscv_state) : «dfn'SLTIU» (1,0,2048) (fixture s 0 17 19) =
 (let t := fixture s 0 17 19; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (2048 : BitVec 12))], 1) (fixture s 0 17 19) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (2048 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_0_8_7
example (s : riscv_state) : «dfn'SLTIU» (7,0,2048) (fixture s 0 17 19) =
 (let t := fixture s 0 17 19; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (2048 : BitVec 12))], 7) (fixture s 0 17 19) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.signExtend 64 (2048 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_0_9_0
example (s : riscv_state) : «dfn'SLTIU» (0,1,0) (fixture s 0 9223372036854775808 19) =
 (let t := fixture s 0 9223372036854775808 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.signExtend 64 (0 : BitVec 12))], 0) (fixture s 0 9223372036854775808 19) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.signExtend 64 (0 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_0_9_1
example (s : riscv_state) : «dfn'SLTIU» (1,1,0) (fixture s 0 9223372036854775808 19) =
 (let t := fixture s 0 9223372036854775808 19; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.signExtend 64 (0 : BitVec 12))], 1) (fixture s 0 9223372036854775808 19) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.signExtend 64 (0 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_0_9_7
example (s : riscv_state) : «dfn'SLTIU» (7,1,0) (fixture s 0 9223372036854775808 19) =
 (let t := fixture s 0 9223372036854775808 19; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.signExtend 64 (0 : BitVec 12))], 7) (fixture s 0 9223372036854775808 19) = _
  have numeric : holV2w 64 [BitVec.ult (BitVec.signExtend 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.signExtend 64 (0 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_2_0_0
example (s : riscv_state) : «dfn'SLTIU» (0,1,0) (fixture s 2 0 19) =
 (let t := fixture s 2 0 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (0 : BitVec 64) (BitVec.signExtend 64 (0 : BitVec 12))], 0) (fixture s 2 0 19) = _
  have numeric : holV2w 64 [BitVec.ult (0 : BitVec 64) (BitVec.signExtend 64 (0 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_2_0_1
example (s : riscv_state) : «dfn'SLTIU» (1,1,0) (fixture s 2 0 19) =
 (let t := fixture s 2 0 19; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (0 : BitVec 64) (BitVec.signExtend 64 (0 : BitVec 12))], 1) (fixture s 2 0 19) = _
  have numeric : holV2w 64 [BitVec.ult (0 : BitVec 64) (BitVec.signExtend 64 (0 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_2_0_7
example (s : riscv_state) : «dfn'SLTIU» (7,1,0) (fixture s 2 0 19) =
 (let t := fixture s 2 0 19; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (0 : BitVec 64) (BitVec.signExtend 64 (0 : BitVec 12))], 7) (fixture s 2 0 19) = _
  have numeric : holV2w 64 [BitVec.ult (0 : BitVec 64) (BitVec.signExtend 64 (0 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_2_1_0
example (s : riscv_state) : «dfn'SLTIU» (0,1,1) (fixture s 2 0 19) =
 (let t := fixture s 2 0 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (0 : BitVec 64) (BitVec.signExtend 64 (1 : BitVec 12))], 0) (fixture s 2 0 19) = _
  have numeric : holV2w 64 [BitVec.ult (0 : BitVec 64) (BitVec.signExtend 64 (1 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_2_1_1
example (s : riscv_state) : «dfn'SLTIU» (1,1,1) (fixture s 2 0 19) =
 (let t := fixture s 2 0 19; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (0 : BitVec 64) (BitVec.signExtend 64 (1 : BitVec 12))], 1) (fixture s 2 0 19) = _
  have numeric : holV2w 64 [BitVec.ult (0 : BitVec 64) (BitVec.signExtend 64 (1 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_2_1_7
example (s : riscv_state) : «dfn'SLTIU» (7,1,1) (fixture s 2 0 19) =
 (let t := fixture s 2 0 19; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (0 : BitVec 64) (BitVec.signExtend 64 (1 : BitVec 12))], 7) (fixture s 2 0 19) = _
  have numeric : holV2w 64 [BitVec.ult (0 : BitVec 64) (BitVec.signExtend 64 (1 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_2_2_0
example (s : riscv_state) : «dfn'SLTIU» (0,1,4095) (fixture s 2 0 19) =
 (let t := fixture s 2 0 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (0 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))], 0) (fixture s 2 0 19) = _
  have numeric : holV2w 64 [BitVec.ult (0 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_2_2_1
example (s : riscv_state) : «dfn'SLTIU» (1,1,4095) (fixture s 2 0 19) =
 (let t := fixture s 2 0 19; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (0 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))], 1) (fixture s 2 0 19) = _
  have numeric : holV2w 64 [BitVec.ult (0 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_2_2_7
example (s : riscv_state) : «dfn'SLTIU» (7,1,4095) (fixture s 2 0 19) =
 (let t := fixture s 2 0 19; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (0 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))], 7) (fixture s 2 0 19) = _
  have numeric : holV2w 64 [BitVec.ult (0 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_2_3_0
example (s : riscv_state) : «dfn'SLTIU» (0,1,4095) (fixture s 2 18446744073709551615 19) =
 (let t := fixture s 2 18446744073709551615 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (18446744073709551615 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))], 0) (fixture s 2 18446744073709551615 19) = _
  have numeric : holV2w 64 [BitVec.ult (18446744073709551615 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_2_3_1
example (s : riscv_state) : «dfn'SLTIU» (1,1,4095) (fixture s 2 18446744073709551615 19) =
 (let t := fixture s 2 18446744073709551615 19; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (18446744073709551615 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))], 1) (fixture s 2 18446744073709551615 19) = _
  have numeric : holV2w 64 [BitVec.ult (18446744073709551615 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_2_3_7
example (s : riscv_state) : «dfn'SLTIU» (7,1,4095) (fixture s 2 18446744073709551615 19) =
 (let t := fixture s 2 18446744073709551615 19; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (18446744073709551615 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))], 7) (fixture s 2 18446744073709551615 19) = _
  have numeric : holV2w 64 [BitVec.ult (18446744073709551615 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_2_4_0
example (s : riscv_state) : «dfn'SLTIU» (0,1,2047) (fixture s 2 2147483647 19) =
 (let t := fixture s 2 2147483647 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (2147483647 : BitVec 64) (BitVec.signExtend 64 (2047 : BitVec 12))], 0) (fixture s 2 2147483647 19) = _
  have numeric : holV2w 64 [BitVec.ult (2147483647 : BitVec 64) (BitVec.signExtend 64 (2047 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_2_4_1
example (s : riscv_state) : «dfn'SLTIU» (1,1,2047) (fixture s 2 2147483647 19) =
 (let t := fixture s 2 2147483647 19; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (2147483647 : BitVec 64) (BitVec.signExtend 64 (2047 : BitVec 12))], 1) (fixture s 2 2147483647 19) = _
  have numeric : holV2w 64 [BitVec.ult (2147483647 : BitVec 64) (BitVec.signExtend 64 (2047 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_2_4_7
example (s : riscv_state) : «dfn'SLTIU» (7,1,2047) (fixture s 2 2147483647 19) =
 (let t := fixture s 2 2147483647 19; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (2147483647 : BitVec 64) (BitVec.signExtend 64 (2047 : BitVec 12))], 7) (fixture s 2 2147483647 19) = _
  have numeric : holV2w 64 [BitVec.ult (2147483647 : BitVec 64) (BitVec.signExtend 64 (2047 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_2_5_0
example (s : riscv_state) : «dfn'SLTIU» (0,1,2048) (fixture s 2 2147483648 19) =
 (let t := fixture s 2 2147483648 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (2147483648 : BitVec 64) (BitVec.signExtend 64 (2048 : BitVec 12))], 0) (fixture s 2 2147483648 19) = _
  have numeric : holV2w 64 [BitVec.ult (2147483648 : BitVec 64) (BitVec.signExtend 64 (2048 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_2_5_1
example (s : riscv_state) : «dfn'SLTIU» (1,1,2048) (fixture s 2 2147483648 19) =
 (let t := fixture s 2 2147483648 19; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (2147483648 : BitVec 64) (BitVec.signExtend 64 (2048 : BitVec 12))], 1) (fixture s 2 2147483648 19) = _
  have numeric : holV2w 64 [BitVec.ult (2147483648 : BitVec 64) (BitVec.signExtend 64 (2048 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_2_5_7
example (s : riscv_state) : «dfn'SLTIU» (7,1,2048) (fixture s 2 2147483648 19) =
 (let t := fixture s 2 2147483648 19; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (2147483648 : BitVec 64) (BitVec.signExtend 64 (2048 : BitVec 12))], 7) (fixture s 2 2147483648 19) = _
  have numeric : holV2w 64 [BitVec.ult (2147483648 : BitVec 64) (BitVec.signExtend 64 (2048 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_2_6_0
example (s : riscv_state) : «dfn'SLTIU» (0,1,4095) (fixture s 2 4294967295 19) =
 (let t := fixture s 2 4294967295 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (4294967295 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))], 0) (fixture s 2 4294967295 19) = _
  have numeric : holV2w 64 [BitVec.ult (4294967295 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_2_6_1
example (s : riscv_state) : «dfn'SLTIU» (1,1,4095) (fixture s 2 4294967295 19) =
 (let t := fixture s 2 4294967295 19; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (4294967295 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))], 1) (fixture s 2 4294967295 19) = _
  have numeric : holV2w 64 [BitVec.ult (4294967295 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_2_6_7
example (s : riscv_state) : «dfn'SLTIU» (7,1,4095) (fixture s 2 4294967295 19) =
 (let t := fixture s 2 4294967295 19; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (4294967295 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))], 7) (fixture s 2 4294967295 19) = _
  have numeric : holV2w 64 [BitVec.ult (4294967295 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_2_7_0
example (s : riscv_state) : «dfn'SLTIU» (0,1,1) (fixture s 2 4294967297 19) =
 (let t := fixture s 2 4294967297 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (4294967297 : BitVec 64) (BitVec.signExtend 64 (1 : BitVec 12))], 0) (fixture s 2 4294967297 19) = _
  have numeric : holV2w 64 [BitVec.ult (4294967297 : BitVec 64) (BitVec.signExtend 64 (1 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_2_7_1
example (s : riscv_state) : «dfn'SLTIU» (1,1,1) (fixture s 2 4294967297 19) =
 (let t := fixture s 2 4294967297 19; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (4294967297 : BitVec 64) (BitVec.signExtend 64 (1 : BitVec 12))], 1) (fixture s 2 4294967297 19) = _
  have numeric : holV2w 64 [BitVec.ult (4294967297 : BitVec 64) (BitVec.signExtend 64 (1 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_2_7_7
example (s : riscv_state) : «dfn'SLTIU» (7,1,1) (fixture s 2 4294967297 19) =
 (let t := fixture s 2 4294967297 19; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (4294967297 : BitVec 64) (BitVec.signExtend 64 (1 : BitVec 12))], 7) (fixture s 2 4294967297 19) = _
  have numeric : holV2w 64 [BitVec.ult (4294967297 : BitVec 64) (BitVec.signExtend 64 (1 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_2_8_0
example (s : riscv_state) : «dfn'SLTIU» (0,0,2048) (fixture s 2 17 19) =
 (let t := fixture s 2 17 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (0 : BitVec 64) (BitVec.signExtend 64 (2048 : BitVec 12))], 0) (fixture s 2 17 19) = _
  have numeric : holV2w 64 [BitVec.ult (0 : BitVec 64) (BitVec.signExtend 64 (2048 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_2_8_1
example (s : riscv_state) : «dfn'SLTIU» (1,0,2048) (fixture s 2 17 19) =
 (let t := fixture s 2 17 19; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (0 : BitVec 64) (BitVec.signExtend 64 (2048 : BitVec 12))], 1) (fixture s 2 17 19) = _
  have numeric : holV2w 64 [BitVec.ult (0 : BitVec 64) (BitVec.signExtend 64 (2048 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_2_8_7
example (s : riscv_state) : «dfn'SLTIU» (7,0,2048) (fixture s 2 17 19) =
 (let t := fixture s 2 17 19; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (0 : BitVec 64) (BitVec.signExtend 64 (2048 : BitVec 12))], 7) (fixture s 2 17 19) = _
  have numeric : holV2w 64 [BitVec.ult (0 : BitVec 64) (BitVec.signExtend 64 (2048 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_2_9_0
example (s : riscv_state) : «dfn'SLTIU» (0,1,0) (fixture s 2 9223372036854775808 19) =
 (let t := fixture s 2 9223372036854775808 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (9223372036854775808 : BitVec 64) (BitVec.signExtend 64 (0 : BitVec 12))], 0) (fixture s 2 9223372036854775808 19) = _
  have numeric : holV2w 64 [BitVec.ult (9223372036854775808 : BitVec 64) (BitVec.signExtend 64 (0 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_2_9_1
example (s : riscv_state) : «dfn'SLTIU» (1,1,0) (fixture s 2 9223372036854775808 19) =
 (let t := fixture s 2 9223372036854775808 19; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (9223372036854775808 : BitVec 64) (BitVec.signExtend 64 (0 : BitVec 12))], 1) (fixture s 2 9223372036854775808 19) = _
  have numeric : holV2w 64 [BitVec.ult (9223372036854775808 : BitVec 64) (BitVec.signExtend 64 (0 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_2_9_7
example (s : riscv_state) : «dfn'SLTIU» (7,1,0) (fixture s 2 9223372036854775808 19) =
 (let t := fixture s 2 9223372036854775808 19; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (9223372036854775808 : BitVec 64) (BitVec.signExtend 64 (0 : BitVec 12))], 7) (fixture s 2 9223372036854775808 19) = _
  have numeric : holV2w 64 [BitVec.ult (9223372036854775808 : BitVec 64) (BitVec.signExtend 64 (0 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_3_0_0
example (s : riscv_state) : «dfn'SLTIU» (0,1,0) (fixture s 3 0 19) =
 (let t := fixture s 3 0 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (0 : BitVec 64) (BitVec.signExtend 64 (0 : BitVec 12))], 0) (fixture s 3 0 19) = _
  have numeric : holV2w 64 [BitVec.ult (0 : BitVec 64) (BitVec.signExtend 64 (0 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_3_0_1
example (s : riscv_state) : «dfn'SLTIU» (1,1,0) (fixture s 3 0 19) =
 (let t := fixture s 3 0 19; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (0 : BitVec 64) (BitVec.signExtend 64 (0 : BitVec 12))], 1) (fixture s 3 0 19) = _
  have numeric : holV2w 64 [BitVec.ult (0 : BitVec 64) (BitVec.signExtend 64 (0 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_3_0_7
example (s : riscv_state) : «dfn'SLTIU» (7,1,0) (fixture s 3 0 19) =
 (let t := fixture s 3 0 19; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (0 : BitVec 64) (BitVec.signExtend 64 (0 : BitVec 12))], 7) (fixture s 3 0 19) = _
  have numeric : holV2w 64 [BitVec.ult (0 : BitVec 64) (BitVec.signExtend 64 (0 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_3_1_0
example (s : riscv_state) : «dfn'SLTIU» (0,1,1) (fixture s 3 0 19) =
 (let t := fixture s 3 0 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (0 : BitVec 64) (BitVec.signExtend 64 (1 : BitVec 12))], 0) (fixture s 3 0 19) = _
  have numeric : holV2w 64 [BitVec.ult (0 : BitVec 64) (BitVec.signExtend 64 (1 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_3_1_1
example (s : riscv_state) : «dfn'SLTIU» (1,1,1) (fixture s 3 0 19) =
 (let t := fixture s 3 0 19; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (0 : BitVec 64) (BitVec.signExtend 64 (1 : BitVec 12))], 1) (fixture s 3 0 19) = _
  have numeric : holV2w 64 [BitVec.ult (0 : BitVec 64) (BitVec.signExtend 64 (1 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_3_1_7
example (s : riscv_state) : «dfn'SLTIU» (7,1,1) (fixture s 3 0 19) =
 (let t := fixture s 3 0 19; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (0 : BitVec 64) (BitVec.signExtend 64 (1 : BitVec 12))], 7) (fixture s 3 0 19) = _
  have numeric : holV2w 64 [BitVec.ult (0 : BitVec 64) (BitVec.signExtend 64 (1 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_3_2_0
example (s : riscv_state) : «dfn'SLTIU» (0,1,4095) (fixture s 3 0 19) =
 (let t := fixture s 3 0 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (0 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))], 0) (fixture s 3 0 19) = _
  have numeric : holV2w 64 [BitVec.ult (0 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_3_2_1
example (s : riscv_state) : «dfn'SLTIU» (1,1,4095) (fixture s 3 0 19) =
 (let t := fixture s 3 0 19; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (0 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))], 1) (fixture s 3 0 19) = _
  have numeric : holV2w 64 [BitVec.ult (0 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_3_2_7
example (s : riscv_state) : «dfn'SLTIU» (7,1,4095) (fixture s 3 0 19) =
 (let t := fixture s 3 0 19; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (0 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))], 7) (fixture s 3 0 19) = _
  have numeric : holV2w 64 [BitVec.ult (0 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_3_3_0
example (s : riscv_state) : «dfn'SLTIU» (0,1,4095) (fixture s 3 18446744073709551615 19) =
 (let t := fixture s 3 18446744073709551615 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (18446744073709551615 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))], 0) (fixture s 3 18446744073709551615 19) = _
  have numeric : holV2w 64 [BitVec.ult (18446744073709551615 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_3_3_1
example (s : riscv_state) : «dfn'SLTIU» (1,1,4095) (fixture s 3 18446744073709551615 19) =
 (let t := fixture s 3 18446744073709551615 19; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (18446744073709551615 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))], 1) (fixture s 3 18446744073709551615 19) = _
  have numeric : holV2w 64 [BitVec.ult (18446744073709551615 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_3_3_7
example (s : riscv_state) : «dfn'SLTIU» (7,1,4095) (fixture s 3 18446744073709551615 19) =
 (let t := fixture s 3 18446744073709551615 19; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (18446744073709551615 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))], 7) (fixture s 3 18446744073709551615 19) = _
  have numeric : holV2w 64 [BitVec.ult (18446744073709551615 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_3_4_0
example (s : riscv_state) : «dfn'SLTIU» (0,1,2047) (fixture s 3 2147483647 19) =
 (let t := fixture s 3 2147483647 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (2147483647 : BitVec 64) (BitVec.signExtend 64 (2047 : BitVec 12))], 0) (fixture s 3 2147483647 19) = _
  have numeric : holV2w 64 [BitVec.ult (2147483647 : BitVec 64) (BitVec.signExtend 64 (2047 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_3_4_1
example (s : riscv_state) : «dfn'SLTIU» (1,1,2047) (fixture s 3 2147483647 19) =
 (let t := fixture s 3 2147483647 19; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (2147483647 : BitVec 64) (BitVec.signExtend 64 (2047 : BitVec 12))], 1) (fixture s 3 2147483647 19) = _
  have numeric : holV2w 64 [BitVec.ult (2147483647 : BitVec 64) (BitVec.signExtend 64 (2047 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_3_4_7
example (s : riscv_state) : «dfn'SLTIU» (7,1,2047) (fixture s 3 2147483647 19) =
 (let t := fixture s 3 2147483647 19; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (2147483647 : BitVec 64) (BitVec.signExtend 64 (2047 : BitVec 12))], 7) (fixture s 3 2147483647 19) = _
  have numeric : holV2w 64 [BitVec.ult (2147483647 : BitVec 64) (BitVec.signExtend 64 (2047 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_3_5_0
example (s : riscv_state) : «dfn'SLTIU» (0,1,2048) (fixture s 3 2147483648 19) =
 (let t := fixture s 3 2147483648 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (2147483648 : BitVec 64) (BitVec.signExtend 64 (2048 : BitVec 12))], 0) (fixture s 3 2147483648 19) = _
  have numeric : holV2w 64 [BitVec.ult (2147483648 : BitVec 64) (BitVec.signExtend 64 (2048 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_3_5_1
example (s : riscv_state) : «dfn'SLTIU» (1,1,2048) (fixture s 3 2147483648 19) =
 (let t := fixture s 3 2147483648 19; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (2147483648 : BitVec 64) (BitVec.signExtend 64 (2048 : BitVec 12))], 1) (fixture s 3 2147483648 19) = _
  have numeric : holV2w 64 [BitVec.ult (2147483648 : BitVec 64) (BitVec.signExtend 64 (2048 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_3_5_7
example (s : riscv_state) : «dfn'SLTIU» (7,1,2048) (fixture s 3 2147483648 19) =
 (let t := fixture s 3 2147483648 19; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (2147483648 : BitVec 64) (BitVec.signExtend 64 (2048 : BitVec 12))], 7) (fixture s 3 2147483648 19) = _
  have numeric : holV2w 64 [BitVec.ult (2147483648 : BitVec 64) (BitVec.signExtend 64 (2048 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_3_6_0
example (s : riscv_state) : «dfn'SLTIU» (0,1,4095) (fixture s 3 4294967295 19) =
 (let t := fixture s 3 4294967295 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (4294967295 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))], 0) (fixture s 3 4294967295 19) = _
  have numeric : holV2w 64 [BitVec.ult (4294967295 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_3_6_1
example (s : riscv_state) : «dfn'SLTIU» (1,1,4095) (fixture s 3 4294967295 19) =
 (let t := fixture s 3 4294967295 19; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (4294967295 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))], 1) (fixture s 3 4294967295 19) = _
  have numeric : holV2w 64 [BitVec.ult (4294967295 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_3_6_7
example (s : riscv_state) : «dfn'SLTIU» (7,1,4095) (fixture s 3 4294967295 19) =
 (let t := fixture s 3 4294967295 19; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (4294967295 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))], 7) (fixture s 3 4294967295 19) = _
  have numeric : holV2w 64 [BitVec.ult (4294967295 : BitVec 64) (BitVec.signExtend 64 (4095 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_3_7_0
example (s : riscv_state) : «dfn'SLTIU» (0,1,1) (fixture s 3 4294967297 19) =
 (let t := fixture s 3 4294967297 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (4294967297 : BitVec 64) (BitVec.signExtend 64 (1 : BitVec 12))], 0) (fixture s 3 4294967297 19) = _
  have numeric : holV2w 64 [BitVec.ult (4294967297 : BitVec 64) (BitVec.signExtend 64 (1 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_3_7_1
example (s : riscv_state) : «dfn'SLTIU» (1,1,1) (fixture s 3 4294967297 19) =
 (let t := fixture s 3 4294967297 19; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (4294967297 : BitVec 64) (BitVec.signExtend 64 (1 : BitVec 12))], 1) (fixture s 3 4294967297 19) = _
  have numeric : holV2w 64 [BitVec.ult (4294967297 : BitVec 64) (BitVec.signExtend 64 (1 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_3_7_7
example (s : riscv_state) : «dfn'SLTIU» (7,1,1) (fixture s 3 4294967297 19) =
 (let t := fixture s 3 4294967297 19; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (4294967297 : BitVec 64) (BitVec.signExtend 64 (1 : BitVec 12))], 7) (fixture s 3 4294967297 19) = _
  have numeric : holV2w 64 [BitVec.ult (4294967297 : BitVec 64) (BitVec.signExtend 64 (1 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_3_8_0
example (s : riscv_state) : «dfn'SLTIU» (0,0,2048) (fixture s 3 17 19) =
 (let t := fixture s 3 17 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (0 : BitVec 64) (BitVec.signExtend 64 (2048 : BitVec 12))], 0) (fixture s 3 17 19) = _
  have numeric : holV2w 64 [BitVec.ult (0 : BitVec 64) (BitVec.signExtend 64 (2048 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_3_8_1
example (s : riscv_state) : «dfn'SLTIU» (1,0,2048) (fixture s 3 17 19) =
 (let t := fixture s 3 17 19; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (0 : BitVec 64) (BitVec.signExtend 64 (2048 : BitVec 12))], 1) (fixture s 3 17 19) = _
  have numeric : holV2w 64 [BitVec.ult (0 : BitVec 64) (BitVec.signExtend 64 (2048 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_3_8_7
example (s : riscv_state) : «dfn'SLTIU» (7,0,2048) (fixture s 3 17 19) =
 (let t := fixture s 3 17 19; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (0 : BitVec 64) (BitVec.signExtend 64 (2048 : BitVec 12))], 7) (fixture s 3 17 19) = _
  have numeric : holV2w 64 [BitVec.ult (0 : BitVec 64) (BitVec.signExtend 64 (2048 : BitVec 12))] = (1 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_3_9_0
example (s : riscv_state) : «dfn'SLTIU» (0,1,0) (fixture s 3 9223372036854775808 19) =
 (let t := fixture s 3 9223372036854775808 19; t) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (9223372036854775808 : BitVec 64) (BitVec.signExtend 64 (0 : BitVec 12))], 0) (fixture s 3 9223372036854775808 19) = _
  have numeric : holV2w 64 [BitVec.ult (9223372036854775808 : BitVec 64) (BitVec.signExtend 64 (0 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_3_9_1
example (s : riscv_state) : «dfn'SLTIU» (1,1,0) (fixture s 3 9223372036854775808 19) =
 (let t := fixture s 3 9223372036854775808 19; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (9223372036854775808 : BitVec 64) (BitVec.signExtend 64 (0 : BitVec 12))], 1) (fixture s 3 9223372036854775808 19) = _
  have numeric : holV2w 64 [BitVec.ult (9223372036854775808 : BitVec 64) (BitVec.signExtend 64 (0 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

-- set_less_SLTIU_3_9_7
example (s : riscv_state) : «dfn'SLTIU» (7,1,0) (fixture s 3 9223372036854775808 19) =
 (let t := fixture s 3 9223372036854775808 19; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  change «write'GPR» (holV2w 64 [BitVec.ult (9223372036854775808 : BitVec 64) (BitVec.signExtend 64 (0 : BitVec 12))], 7) (fixture s 3 9223372036854775808 19) = _
  have numeric : holV2w 64 [BitVec.ult (9223372036854775808 : BitVec 64) (BitVec.signExtend 64 (0 : BitVec 12))] = (0 : BitVec 64) := by decide
  rw [numeric]
  rfl

private def unknownMessage : List (BitVec 8) :=
 [85,110,107,110,111,119,110,32,97,114,99,104,105,116,101,99,116,117,114,101,58,32,49]

-- set_less_invalid_SLT_0_0
example (s : riscv_state) : «dfn'SLT» (0,0,0) ({fixture s 1 17 19 with exception := exception.NoException}) =
 (let t := {fixture s 1 17 19 with exception := exception.NoException}; let u := {t with exception := exception.UNDEFINED unknownMessage}; u) := by
  have fcpZero : (holFcpWord (fun _ => false) : BitVec 64) = 0 := by decide
  have zero : BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)) = (0 : BitVec 64) := by decide
  simp [«dfn'SLT», fixture, in32BitMode, curArch, architecture, MCSR, raiseException_eq, unknownMessage, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, «write'GPR»]
  all_goals try rw [zero]
  all_goals simp [zero, BitVec.slt, BitVec.ult, holV2w, fcpZero]
  all_goals split <;> rfl

-- set_less_invalid_SLT_0_1
example (s : riscv_state) : «dfn'SLT» (1,0,0) ({fixture s 1 17 19 with exception := exception.NoException}) =
 (let t := {fixture s 1 17 19 with exception := exception.NoException}; let u := {t with exception := exception.UNDEFINED unknownMessage}; {u with c_gpr := holUpdate 7 (holUpdate 1 0 (u.c_gpr 7)) u.c_gpr}) := by
  have fcpZero : (holFcpWord (fun _ => false) : BitVec 64) = 0 := by decide
  have zero : BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)) = (0 : BitVec 64) := by decide
  simp [«dfn'SLT», fixture, in32BitMode, curArch, architecture, MCSR, GPR, raiseException_eq, unknownMessage, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, «write'GPR», «write'gpr»]
  all_goals try rw [zero]
  all_goals simp [BitVec.slt, holV2w, fcpZero]
  all_goals split <;> rfl

-- set_less_invalid_SLT_1_0
example (s : riscv_state) : «dfn'SLT» (0,0,0) ({fixture s 1 17 19 with exception := exception.UNDEFINED [9]}) =
 (let t := {fixture s 1 17 19 with exception := exception.UNDEFINED [9]}; let u := {t with exception := exception.UNDEFINED [9]}; u) := by
  have fcpZero : (holFcpWord (fun _ => false) : BitVec 64) = 0 := by decide
  have zero : BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)) = (0 : BitVec 64) := by decide
  simp [«dfn'SLT», fixture, in32BitMode, curArch, architecture, MCSR, raiseException_eq, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, «write'GPR»]
  all_goals try rw [zero]
  all_goals simp [zero, BitVec.slt, BitVec.ult, holV2w, fcpZero]
  all_goals split <;> rfl

-- set_less_invalid_SLT_1_1
example (s : riscv_state) : «dfn'SLT» (1,0,0) ({fixture s 1 17 19 with exception := exception.UNDEFINED [9]}) =
 (let t := {fixture s 1 17 19 with exception := exception.UNDEFINED [9]}; let u := {t with exception := exception.UNDEFINED [9]}; {u with c_gpr := holUpdate 7 (holUpdate 1 0 (u.c_gpr 7)) u.c_gpr}) := by
  have fcpZero : (holFcpWord (fun _ => false) : BitVec 64) = 0 := by decide
  have zero : BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)) = (0 : BitVec 64) := by decide
  simp [«dfn'SLT», fixture, in32BitMode, curArch, architecture, MCSR, GPR, raiseException_eq, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, «write'GPR», «write'gpr»]
  all_goals try rw [zero]
  all_goals simp [BitVec.slt, holV2w, fcpZero]
  all_goals split <;> rfl

-- set_less_invalid_SLTU_0_0
example (s : riscv_state) : «dfn'SLTU» (0,0,0) ({fixture s 1 17 19 with exception := exception.NoException}) =
 (let t := {fixture s 1 17 19 with exception := exception.NoException}; let u := {t with exception := exception.UNDEFINED unknownMessage}; u) := by
  have fcpZero : (holFcpWord (fun _ => false) : BitVec 64) = 0 := by decide
  have zero : BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)) = (0 : BitVec 64) := by decide
  simp [«dfn'SLTU», fixture, in32BitMode, curArch, architecture, MCSR, raiseException_eq, unknownMessage, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, «write'GPR»]
  all_goals try rw [zero]
  all_goals simp [zero, BitVec.slt, BitVec.ult, holV2w, fcpZero]
  all_goals split <;> rfl

-- set_less_invalid_SLTU_0_1
example (s : riscv_state) : «dfn'SLTU» (1,0,0) ({fixture s 1 17 19 with exception := exception.NoException}) =
 (let t := {fixture s 1 17 19 with exception := exception.NoException}; let u := {t with exception := exception.UNDEFINED unknownMessage}; {u with c_gpr := holUpdate 7 (holUpdate 1 0 (u.c_gpr 7)) u.c_gpr}) := by
  have fcpZero : (holFcpWord (fun _ => false) : BitVec 64) = 0 := by decide
  have zero : BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)) = (0 : BitVec 64) := by decide
  simp [«dfn'SLTU», fixture, in32BitMode, curArch, architecture, MCSR, GPR, raiseException_eq, unknownMessage, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, «write'GPR», «write'gpr»]
  all_goals try rw [zero]
  all_goals simp [BitVec.ult, holV2w, fcpZero]
  all_goals split <;> rfl

-- set_less_invalid_SLTU_1_0
example (s : riscv_state) : «dfn'SLTU» (0,0,0) ({fixture s 1 17 19 with exception := exception.UNDEFINED [9]}) =
 (let t := {fixture s 1 17 19 with exception := exception.UNDEFINED [9]}; let u := {t with exception := exception.UNDEFINED [9]}; u) := by
  have fcpZero : (holFcpWord (fun _ => false) : BitVec 64) = 0 := by decide
  have zero : BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)) = (0 : BitVec 64) := by decide
  simp [«dfn'SLTU», fixture, in32BitMode, curArch, architecture, MCSR, raiseException_eq, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, «write'GPR»]
  all_goals try rw [zero]
  all_goals simp [zero, BitVec.slt, BitVec.ult, holV2w, fcpZero]
  all_goals split <;> rfl

-- set_less_invalid_SLTU_1_1
example (s : riscv_state) : «dfn'SLTU» (1,0,0) ({fixture s 1 17 19 with exception := exception.UNDEFINED [9]}) =
 (let t := {fixture s 1 17 19 with exception := exception.UNDEFINED [9]}; let u := {t with exception := exception.UNDEFINED [9]}; {u with c_gpr := holUpdate 7 (holUpdate 1 0 (u.c_gpr 7)) u.c_gpr}) := by
  have fcpZero : (holFcpWord (fun _ => false) : BitVec 64) = 0 := by decide
  have zero : BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)) = (0 : BitVec 64) := by decide
  simp [«dfn'SLTU», fixture, in32BitMode, curArch, architecture, MCSR, GPR, raiseException_eq, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, «write'GPR», «write'gpr»]
  all_goals try rw [zero]
  all_goals simp [BitVec.ult, holV2w, fcpZero]
  all_goals split <;> rfl

-- set_less_invalid_SLTI_0_0
example (s : riscv_state) : «dfn'SLTI» (0,0,0) ({fixture s 1 17 19 with exception := exception.NoException}) =
 (let t := {fixture s 1 17 19 with exception := exception.NoException}; let u := {t with exception := exception.UNDEFINED unknownMessage}; u) := by
  have fcpZero : (holFcpWord (fun _ => false) : BitVec 64) = 0 := by decide
  have zero : BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)) = (0 : BitVec 64) := by decide
  simp [«dfn'SLTI», fixture, in32BitMode, curArch, architecture, MCSR, raiseException_eq, unknownMessage, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, «write'GPR»]
  all_goals try rw [zero]
  all_goals simp [zero, BitVec.slt, BitVec.ult, holV2w, fcpZero]
  all_goals split <;> rfl

-- set_less_invalid_SLTI_0_1
example (s : riscv_state) : «dfn'SLTI» (1,0,0) ({fixture s 1 17 19 with exception := exception.NoException}) =
 (let t := {fixture s 1 17 19 with exception := exception.NoException}; let u := {t with exception := exception.UNDEFINED unknownMessage}; {u with c_gpr := holUpdate 7 (holUpdate 1 0 (u.c_gpr 7)) u.c_gpr}) := by
  have fcpZero : (holFcpWord (fun _ => false) : BitVec 64) = 0 := by decide
  have zero : BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)) = (0 : BitVec 64) := by decide
  simp [«dfn'SLTI», fixture, in32BitMode, curArch, architecture, MCSR, GPR, raiseException_eq, unknownMessage, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, «write'GPR», «write'gpr»]
  all_goals try rw [zero]
  all_goals simp [BitVec.slt, holV2w]
  all_goals split <;> rfl

-- set_less_invalid_SLTI_1_0
example (s : riscv_state) : «dfn'SLTI» (0,0,0) ({fixture s 1 17 19 with exception := exception.UNDEFINED [9]}) =
 (let t := {fixture s 1 17 19 with exception := exception.UNDEFINED [9]}; let u := {t with exception := exception.UNDEFINED [9]}; u) := by
  have fcpZero : (holFcpWord (fun _ => false) : BitVec 64) = 0 := by decide
  have zero : BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)) = (0 : BitVec 64) := by decide
  simp [«dfn'SLTI», fixture, in32BitMode, curArch, architecture, MCSR, raiseException_eq, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, «write'GPR»]
  all_goals try rw [zero]
  all_goals simp [zero, BitVec.slt, BitVec.ult, holV2w, fcpZero]
  all_goals split <;> rfl

-- set_less_invalid_SLTI_1_1
example (s : riscv_state) : «dfn'SLTI» (1,0,0) ({fixture s 1 17 19 with exception := exception.UNDEFINED [9]}) =
 (let t := {fixture s 1 17 19 with exception := exception.UNDEFINED [9]}; let u := {t with exception := exception.UNDEFINED [9]}; {u with c_gpr := holUpdate 7 (holUpdate 1 0 (u.c_gpr 7)) u.c_gpr}) := by
  have fcpZero : (holFcpWord (fun _ => false) : BitVec 64) = 0 := by decide
  have zero : BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)) = (0 : BitVec 64) := by decide
  simp [«dfn'SLTI», fixture, in32BitMode, curArch, architecture, MCSR, GPR, raiseException_eq, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, «write'GPR», «write'gpr»]
  all_goals try rw [zero]
  all_goals simp [BitVec.slt, holV2w]
  all_goals split <;> rfl

-- set_less_invalid_SLTIU_0_0
example (s : riscv_state) : «dfn'SLTIU» (0,0,0) ({fixture s 1 17 19 with exception := exception.NoException}) =
 (let t := {fixture s 1 17 19 with exception := exception.NoException}; let u := {t with exception := exception.UNDEFINED unknownMessage}; u) := by
  have fcpZero : (holFcpWord (fun _ => false) : BitVec 64) = 0 := by decide
  have zero : BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)) = (0 : BitVec 64) := by decide
  simp [«dfn'SLTIU», fixture, in32BitMode, curArch, architecture, MCSR, raiseException_eq, unknownMessage, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, «write'GPR»]
  all_goals try rw [zero]
  all_goals simp [zero, BitVec.slt, BitVec.ult, holV2w, fcpZero]
  all_goals split <;> rfl

-- set_less_invalid_SLTIU_0_1
example (s : riscv_state) : «dfn'SLTIU» (1,0,0) ({fixture s 1 17 19 with exception := exception.NoException}) =
 (let t := {fixture s 1 17 19 with exception := exception.NoException}; let u := {t with exception := exception.UNDEFINED unknownMessage}; {u with c_gpr := holUpdate 7 (holUpdate 1 0 (u.c_gpr 7)) u.c_gpr}) := by
  have fcpZero : (holFcpWord (fun _ => false) : BitVec 64) = 0 := by decide
  have zero : BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)) = (0 : BitVec 64) := by decide
  simp [«dfn'SLTIU», fixture, in32BitMode, curArch, architecture, MCSR, GPR, raiseException_eq, unknownMessage, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, «write'GPR», «write'gpr»]
  all_goals try rw [zero]
  all_goals simp [BitVec.ult, holV2w, fcpZero]
  all_goals split <;> rfl

-- set_less_invalid_SLTIU_1_0
example (s : riscv_state) : «dfn'SLTIU» (0,0,0) ({fixture s 1 17 19 with exception := exception.UNDEFINED [9]}) =
 (let t := {fixture s 1 17 19 with exception := exception.UNDEFINED [9]}; let u := {t with exception := exception.UNDEFINED [9]}; u) := by
  have fcpZero : (holFcpWord (fun _ => false) : BitVec 64) = 0 := by decide
  have zero : BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)) = (0 : BitVec 64) := by decide
  simp [«dfn'SLTIU», fixture, in32BitMode, curArch, architecture, MCSR, raiseException_eq, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, «write'GPR»]
  all_goals try rw [zero]
  all_goals simp [zero, BitVec.slt, BitVec.ult, holV2w, fcpZero]
  all_goals split <;> rfl

-- set_less_invalid_SLTIU_1_1
example (s : riscv_state) : «dfn'SLTIU» (1,0,0) ({fixture s 1 17 19 with exception := exception.UNDEFINED [9]}) =
 (let t := {fixture s 1 17 19 with exception := exception.UNDEFINED [9]}; let u := {t with exception := exception.UNDEFINED [9]}; {u with c_gpr := holUpdate 7 (holUpdate 1 0 (u.c_gpr 7)) u.c_gpr}) := by
  have fcpZero : (holFcpWord (fun _ => false) : BitVec 64) = 0 := by decide
  have zero : BitVec.signExtend 64 (holWordExtract 32 31 0 (0 : BitVec 64)) = (0 : BitVec 64) := by decide
  simp [«dfn'SLTIU», fixture, in32BitMode, curArch, architecture, MCSR, GPR, raiseException_eq, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex, «write'GPR», «write'gpr»]
  all_goals try rw [zero]
  all_goals simp [BitVec.ult, holV2w, fcpZero]
  all_goals split <;> rfl

end Flapjack.Test.L3SetLessParity
