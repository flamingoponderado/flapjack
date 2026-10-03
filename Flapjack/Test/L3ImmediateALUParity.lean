import Flapjack.RiscV.L3.Defs.ImmediateALU

namespace Flapjack.Test.L3ImmediateALUParity
open Flapjack.RiscV.L3
private def fixture (s : riscv_state) (a : BitVec 64) : riscv_state :=
 {s with procID := 7, c_gpr := fun id r => if r = 1 then a else s.c_gpr id r}

-- immediate_alu_ADDI_0_0
example (s : riscv_state) : «dfn'ADDI» (0,1,0) (fixture s 0) =
 (let t := fixture s 0; t) := by
  rfl

-- immediate_alu_ADDI_0_1
example (s : riscv_state) : «dfn'ADDI» (1,1,0) (fixture s 0) =
 (let t := fixture s 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) + (BitVec.signExtend 64 (0 : BitVec 12))) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'ADDI» (1,1,0) (fixture s 0) = (let t := fixture s 0; {t with c_gpr := holUpdate 7 (holUpdate 1 ((0 : BitVec 64) + (BitVec.signExtend 64 (0 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ADDI_0_7
example (s : riscv_state) : «dfn'ADDI» (7,1,0) (fixture s 0) =
 (let t := fixture s 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) + (BitVec.signExtend 64 (0 : BitVec 12))) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'ADDI» (7,1,0) (fixture s 0) = (let t := fixture s 0; {t with c_gpr := holUpdate 7 (holUpdate 7 ((0 : BitVec 64) + (BitVec.signExtend 64 (0 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ADDI_1_0
example (s : riscv_state) : «dfn'ADDI» (0,1,1) (fixture s 18446744073709551615) =
 (let t := fixture s 18446744073709551615; t) := by
  rfl

-- immediate_alu_ADDI_1_1
example (s : riscv_state) : «dfn'ADDI» (1,1,1) (fixture s 18446744073709551615) =
 (let t := fixture s 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((18446744073709551615 : BitVec 64) + (BitVec.signExtend 64 (1 : BitVec 12))) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'ADDI» (1,1,1) (fixture s 18446744073709551615) = (let t := fixture s 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 ((18446744073709551615 : BitVec 64) + (BitVec.signExtend 64 (1 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ADDI_1_7
example (s : riscv_state) : «dfn'ADDI» (7,1,1) (fixture s 18446744073709551615) =
 (let t := fixture s 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((18446744073709551615 : BitVec 64) + (BitVec.signExtend 64 (1 : BitVec 12))) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'ADDI» (7,1,1) (fixture s 18446744073709551615) = (let t := fixture s 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 ((18446744073709551615 : BitVec 64) + (BitVec.signExtend 64 (1 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ADDI_2_0
example (s : riscv_state) : «dfn'ADDI» (0,1,4095) (fixture s 0) =
 (let t := fixture s 0; t) := by
  rfl

-- immediate_alu_ADDI_2_1
example (s : riscv_state) : «dfn'ADDI» (1,1,4095) (fixture s 0) =
 (let t := fixture s 0; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) + (BitVec.signExtend 64 (4095 : BitVec 12))) = (18446744073709551615 : BitVec 64) := by decide
  have symbolic := (show «dfn'ADDI» (1,1,4095) (fixture s 0) = (let t := fixture s 0; {t with c_gpr := holUpdate 7 (holUpdate 1 ((0 : BitVec 64) + (BitVec.signExtend 64 (4095 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ADDI_2_7
example (s : riscv_state) : «dfn'ADDI» (7,1,4095) (fixture s 0) =
 (let t := fixture s 0; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) + (BitVec.signExtend 64 (4095 : BitVec 12))) = (18446744073709551615 : BitVec 64) := by decide
  have symbolic := (show «dfn'ADDI» (7,1,4095) (fixture s 0) = (let t := fixture s 0; {t with c_gpr := holUpdate 7 (holUpdate 7 ((0 : BitVec 64) + (BitVec.signExtend 64 (4095 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ADDI_3_0
example (s : riscv_state) : «dfn'ADDI» (0,1,2048) (fixture s 9223372036854775808) =
 (let t := fixture s 9223372036854775808; t) := by
  rfl

-- immediate_alu_ADDI_3_1
example (s : riscv_state) : «dfn'ADDI» (1,1,2048) (fixture s 9223372036854775808) =
 (let t := fixture s 9223372036854775808; {t with c_gpr := holUpdate 7 (holUpdate 1 9223372036854773760 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((9223372036854775808 : BitVec 64) + (BitVec.signExtend 64 (2048 : BitVec 12))) = (9223372036854773760 : BitVec 64) := by decide
  have symbolic := (show «dfn'ADDI» (1,1,2048) (fixture s 9223372036854775808) = (let t := fixture s 9223372036854775808; {t with c_gpr := holUpdate 7 (holUpdate 1 ((9223372036854775808 : BitVec 64) + (BitVec.signExtend 64 (2048 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ADDI_3_7
example (s : riscv_state) : «dfn'ADDI» (7,1,2048) (fixture s 9223372036854775808) =
 (let t := fixture s 9223372036854775808; {t with c_gpr := holUpdate 7 (holUpdate 7 9223372036854773760 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((9223372036854775808 : BitVec 64) + (BitVec.signExtend 64 (2048 : BitVec 12))) = (9223372036854773760 : BitVec 64) := by decide
  have symbolic := (show «dfn'ADDI» (7,1,2048) (fixture s 9223372036854775808) = (let t := fixture s 9223372036854775808; {t with c_gpr := holUpdate 7 (holUpdate 7 ((9223372036854775808 : BitVec 64) + (BitVec.signExtend 64 (2048 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ADDI_4_0
example (s : riscv_state) : «dfn'ADDI» (0,1,2047) (fixture s 12297829382473034410) =
 (let t := fixture s 12297829382473034410; t) := by
  rfl

-- immediate_alu_ADDI_4_1
example (s : riscv_state) : «dfn'ADDI» (1,1,2047) (fixture s 12297829382473034410) =
 (let t := fixture s 12297829382473034410; {t with c_gpr := holUpdate 7 (holUpdate 1 12297829382473036457 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((12297829382473034410 : BitVec 64) + (BitVec.signExtend 64 (2047 : BitVec 12))) = (12297829382473036457 : BitVec 64) := by decide
  have symbolic := (show «dfn'ADDI» (1,1,2047) (fixture s 12297829382473034410) = (let t := fixture s 12297829382473034410; {t with c_gpr := holUpdate 7 (holUpdate 1 ((12297829382473034410 : BitVec 64) + (BitVec.signExtend 64 (2047 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ADDI_4_7
example (s : riscv_state) : «dfn'ADDI» (7,1,2047) (fixture s 12297829382473034410) =
 (let t := fixture s 12297829382473034410; {t with c_gpr := holUpdate 7 (holUpdate 7 12297829382473036457 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((12297829382473034410 : BitVec 64) + (BitVec.signExtend 64 (2047 : BitVec 12))) = (12297829382473036457 : BitVec 64) := by decide
  have symbolic := (show «dfn'ADDI» (7,1,2047) (fixture s 12297829382473034410) = (let t := fixture s 12297829382473034410; {t with c_gpr := holUpdate 7 (holUpdate 7 ((12297829382473034410 : BitVec 64) + (BitVec.signExtend 64 (2047 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ADDI_5_0
example (s : riscv_state) : «dfn'ADDI» (0,1,2048) (fixture s 4294967297) =
 (let t := fixture s 4294967297; t) := by
  rfl

-- immediate_alu_ADDI_5_1
example (s : riscv_state) : «dfn'ADDI» (1,1,2048) (fixture s 4294967297) =
 (let t := fixture s 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 1 4294965249 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((4294967297 : BitVec 64) + (BitVec.signExtend 64 (2048 : BitVec 12))) = (4294965249 : BitVec 64) := by decide
  have symbolic := (show «dfn'ADDI» (1,1,2048) (fixture s 4294967297) = (let t := fixture s 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 1 ((4294967297 : BitVec 64) + (BitVec.signExtend 64 (2048 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ADDI_5_7
example (s : riscv_state) : «dfn'ADDI» (7,1,2048) (fixture s 4294967297) =
 (let t := fixture s 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 7 4294965249 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((4294967297 : BitVec 64) + (BitVec.signExtend 64 (2048 : BitVec 12))) = (4294965249 : BitVec 64) := by decide
  have symbolic := (show «dfn'ADDI» (7,1,2048) (fixture s 4294967297) = (let t := fixture s 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 7 ((4294967297 : BitVec 64) + (BitVec.signExtend 64 (2048 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ADDI_6_0
example (s : riscv_state) : «dfn'ADDI» (0,0,4095) (fixture s 17) =
 (let t := fixture s 17; t) := by
  rfl

-- immediate_alu_ADDI_6_1
example (s : riscv_state) : «dfn'ADDI» (1,0,4095) (fixture s 17) =
 (let t := fixture s 17; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) + (BitVec.signExtend 64 (4095 : BitVec 12))) = (18446744073709551615 : BitVec 64) := by decide
  have symbolic := (show «dfn'ADDI» (1,0,4095) (fixture s 17) = (let t := fixture s 17; {t with c_gpr := holUpdate 7 (holUpdate 1 ((0 : BitVec 64) + (BitVec.signExtend 64 (4095 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ADDI_6_7
example (s : riscv_state) : «dfn'ADDI» (7,0,4095) (fixture s 17) =
 (let t := fixture s 17; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) + (BitVec.signExtend 64 (4095 : BitVec 12))) = (18446744073709551615 : BitVec 64) := by decide
  have symbolic := (show «dfn'ADDI» (7,0,4095) (fixture s 17) = (let t := fixture s 17; {t with c_gpr := holUpdate 7 (holUpdate 7 ((0 : BitVec 64) + (BitVec.signExtend 64 (4095 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ADDI_7_0
example (s : riscv_state) : «dfn'ADDI» (0,0,2048) (fixture s 18446744073709551615) =
 (let t := fixture s 18446744073709551615; t) := by
  rfl

-- immediate_alu_ADDI_7_1
example (s : riscv_state) : «dfn'ADDI» (1,0,2048) (fixture s 18446744073709551615) =
 (let t := fixture s 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709549568 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) + (BitVec.signExtend 64 (2048 : BitVec 12))) = (18446744073709549568 : BitVec 64) := by decide
  have symbolic := (show «dfn'ADDI» (1,0,2048) (fixture s 18446744073709551615) = (let t := fixture s 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 ((0 : BitVec 64) + (BitVec.signExtend 64 (2048 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ADDI_7_7
example (s : riscv_state) : «dfn'ADDI» (7,0,2048) (fixture s 18446744073709551615) =
 (let t := fixture s 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709549568 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) + (BitVec.signExtend 64 (2048 : BitVec 12))) = (18446744073709549568 : BitVec 64) := by decide
  have symbolic := (show «dfn'ADDI» (7,0,2048) (fixture s 18446744073709551615) = (let t := fixture s 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 ((0 : BitVec 64) + (BitVec.signExtend 64 (2048 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ADDI_8_0
example (s : riscv_state) : «dfn'ADDI» (0,1,4095) (fixture s 18446744073709551615) =
 (let t := fixture s 18446744073709551615; t) := by
  rfl

-- immediate_alu_ADDI_8_1
example (s : riscv_state) : «dfn'ADDI» (1,1,4095) (fixture s 18446744073709551615) =
 (let t := fixture s 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((18446744073709551615 : BitVec 64) + (BitVec.signExtend 64 (4095 : BitVec 12))) = (18446744073709551614 : BitVec 64) := by decide
  have symbolic := (show «dfn'ADDI» (1,1,4095) (fixture s 18446744073709551615) = (let t := fixture s 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 ((18446744073709551615 : BitVec 64) + (BitVec.signExtend 64 (4095 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ADDI_8_7
example (s : riscv_state) : «dfn'ADDI» (7,1,4095) (fixture s 18446744073709551615) =
 (let t := fixture s 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((18446744073709551615 : BitVec 64) + (BitVec.signExtend 64 (4095 : BitVec 12))) = (18446744073709551614 : BitVec 64) := by decide
  have symbolic := (show «dfn'ADDI» (7,1,4095) (fixture s 18446744073709551615) = (let t := fixture s 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 ((18446744073709551615 : BitVec 64) + (BitVec.signExtend 64 (4095 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ADDI_9_0
example (s : riscv_state) : «dfn'ADDI» (0,1,1) (fixture s 2147483648) =
 (let t := fixture s 2147483648; t) := by
  rfl

-- immediate_alu_ADDI_9_1
example (s : riscv_state) : «dfn'ADDI» (1,1,1) (fixture s 2147483648) =
 (let t := fixture s 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 1 2147483649 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((2147483648 : BitVec 64) + (BitVec.signExtend 64 (1 : BitVec 12))) = (2147483649 : BitVec 64) := by decide
  have symbolic := (show «dfn'ADDI» (1,1,1) (fixture s 2147483648) = (let t := fixture s 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 1 ((2147483648 : BitVec 64) + (BitVec.signExtend 64 (1 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ADDI_9_7
example (s : riscv_state) : «dfn'ADDI» (7,1,1) (fixture s 2147483648) =
 (let t := fixture s 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 7 2147483649 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((2147483648 : BitVec 64) + (BitVec.signExtend 64 (1 : BitVec 12))) = (2147483649 : BitVec 64) := by decide
  have symbolic := (show «dfn'ADDI» (7,1,1) (fixture s 2147483648) = (let t := fixture s 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 7 ((2147483648 : BitVec 64) + (BitVec.signExtend 64 (1 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ANDI_0_0
example (s : riscv_state) : «dfn'ANDI» (0,1,0) (fixture s 0) =
 (let t := fixture s 0; t) := by
  rfl

-- immediate_alu_ANDI_0_1
example (s : riscv_state) : «dfn'ANDI» (1,1,0) (fixture s 0) =
 (let t := fixture s 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) &&& (BitVec.signExtend 64 (0 : BitVec 12))) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'ANDI» (1,1,0) (fixture s 0) = (let t := fixture s 0; {t with c_gpr := holUpdate 7 (holUpdate 1 ((0 : BitVec 64) &&& (BitVec.signExtend 64 (0 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ANDI_0_7
example (s : riscv_state) : «dfn'ANDI» (7,1,0) (fixture s 0) =
 (let t := fixture s 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) &&& (BitVec.signExtend 64 (0 : BitVec 12))) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'ANDI» (7,1,0) (fixture s 0) = (let t := fixture s 0; {t with c_gpr := holUpdate 7 (holUpdate 7 ((0 : BitVec 64) &&& (BitVec.signExtend 64 (0 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ANDI_1_0
example (s : riscv_state) : «dfn'ANDI» (0,1,1) (fixture s 18446744073709551615) =
 (let t := fixture s 18446744073709551615; t) := by
  rfl

-- immediate_alu_ANDI_1_1
example (s : riscv_state) : «dfn'ANDI» (1,1,1) (fixture s 18446744073709551615) =
 (let t := fixture s 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((18446744073709551615 : BitVec 64) &&& (BitVec.signExtend 64 (1 : BitVec 12))) = (1 : BitVec 64) := by decide
  have symbolic := (show «dfn'ANDI» (1,1,1) (fixture s 18446744073709551615) = (let t := fixture s 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 ((18446744073709551615 : BitVec 64) &&& (BitVec.signExtend 64 (1 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ANDI_1_7
example (s : riscv_state) : «dfn'ANDI» (7,1,1) (fixture s 18446744073709551615) =
 (let t := fixture s 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((18446744073709551615 : BitVec 64) &&& (BitVec.signExtend 64 (1 : BitVec 12))) = (1 : BitVec 64) := by decide
  have symbolic := (show «dfn'ANDI» (7,1,1) (fixture s 18446744073709551615) = (let t := fixture s 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 ((18446744073709551615 : BitVec 64) &&& (BitVec.signExtend 64 (1 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ANDI_2_0
example (s : riscv_state) : «dfn'ANDI» (0,1,4095) (fixture s 0) =
 (let t := fixture s 0; t) := by
  rfl

-- immediate_alu_ANDI_2_1
example (s : riscv_state) : «dfn'ANDI» (1,1,4095) (fixture s 0) =
 (let t := fixture s 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) &&& (BitVec.signExtend 64 (4095 : BitVec 12))) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'ANDI» (1,1,4095) (fixture s 0) = (let t := fixture s 0; {t with c_gpr := holUpdate 7 (holUpdate 1 ((0 : BitVec 64) &&& (BitVec.signExtend 64 (4095 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ANDI_2_7
example (s : riscv_state) : «dfn'ANDI» (7,1,4095) (fixture s 0) =
 (let t := fixture s 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) &&& (BitVec.signExtend 64 (4095 : BitVec 12))) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'ANDI» (7,1,4095) (fixture s 0) = (let t := fixture s 0; {t with c_gpr := holUpdate 7 (holUpdate 7 ((0 : BitVec 64) &&& (BitVec.signExtend 64 (4095 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ANDI_3_0
example (s : riscv_state) : «dfn'ANDI» (0,1,2048) (fixture s 9223372036854775808) =
 (let t := fixture s 9223372036854775808; t) := by
  rfl

-- immediate_alu_ANDI_3_1
example (s : riscv_state) : «dfn'ANDI» (1,1,2048) (fixture s 9223372036854775808) =
 (let t := fixture s 9223372036854775808; {t with c_gpr := holUpdate 7 (holUpdate 1 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((9223372036854775808 : BitVec 64) &&& (BitVec.signExtend 64 (2048 : BitVec 12))) = (9223372036854775808 : BitVec 64) := by decide
  have symbolic := (show «dfn'ANDI» (1,1,2048) (fixture s 9223372036854775808) = (let t := fixture s 9223372036854775808; {t with c_gpr := holUpdate 7 (holUpdate 1 ((9223372036854775808 : BitVec 64) &&& (BitVec.signExtend 64 (2048 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ANDI_3_7
example (s : riscv_state) : «dfn'ANDI» (7,1,2048) (fixture s 9223372036854775808) =
 (let t := fixture s 9223372036854775808; {t with c_gpr := holUpdate 7 (holUpdate 7 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((9223372036854775808 : BitVec 64) &&& (BitVec.signExtend 64 (2048 : BitVec 12))) = (9223372036854775808 : BitVec 64) := by decide
  have symbolic := (show «dfn'ANDI» (7,1,2048) (fixture s 9223372036854775808) = (let t := fixture s 9223372036854775808; {t with c_gpr := holUpdate 7 (holUpdate 7 ((9223372036854775808 : BitVec 64) &&& (BitVec.signExtend 64 (2048 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ANDI_4_0
example (s : riscv_state) : «dfn'ANDI» (0,1,2047) (fixture s 12297829382473034410) =
 (let t := fixture s 12297829382473034410; t) := by
  rfl

-- immediate_alu_ANDI_4_1
example (s : riscv_state) : «dfn'ANDI» (1,1,2047) (fixture s 12297829382473034410) =
 (let t := fixture s 12297829382473034410; {t with c_gpr := holUpdate 7 (holUpdate 1 682 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((12297829382473034410 : BitVec 64) &&& (BitVec.signExtend 64 (2047 : BitVec 12))) = (682 : BitVec 64) := by decide
  have symbolic := (show «dfn'ANDI» (1,1,2047) (fixture s 12297829382473034410) = (let t := fixture s 12297829382473034410; {t with c_gpr := holUpdate 7 (holUpdate 1 ((12297829382473034410 : BitVec 64) &&& (BitVec.signExtend 64 (2047 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ANDI_4_7
example (s : riscv_state) : «dfn'ANDI» (7,1,2047) (fixture s 12297829382473034410) =
 (let t := fixture s 12297829382473034410; {t with c_gpr := holUpdate 7 (holUpdate 7 682 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((12297829382473034410 : BitVec 64) &&& (BitVec.signExtend 64 (2047 : BitVec 12))) = (682 : BitVec 64) := by decide
  have symbolic := (show «dfn'ANDI» (7,1,2047) (fixture s 12297829382473034410) = (let t := fixture s 12297829382473034410; {t with c_gpr := holUpdate 7 (holUpdate 7 ((12297829382473034410 : BitVec 64) &&& (BitVec.signExtend 64 (2047 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ANDI_5_0
example (s : riscv_state) : «dfn'ANDI» (0,1,2048) (fixture s 4294967297) =
 (let t := fixture s 4294967297; t) := by
  rfl

-- immediate_alu_ANDI_5_1
example (s : riscv_state) : «dfn'ANDI» (1,1,2048) (fixture s 4294967297) =
 (let t := fixture s 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 1 4294967296 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((4294967297 : BitVec 64) &&& (BitVec.signExtend 64 (2048 : BitVec 12))) = (4294967296 : BitVec 64) := by decide
  have symbolic := (show «dfn'ANDI» (1,1,2048) (fixture s 4294967297) = (let t := fixture s 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 1 ((4294967297 : BitVec 64) &&& (BitVec.signExtend 64 (2048 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ANDI_5_7
example (s : riscv_state) : «dfn'ANDI» (7,1,2048) (fixture s 4294967297) =
 (let t := fixture s 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 7 4294967296 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((4294967297 : BitVec 64) &&& (BitVec.signExtend 64 (2048 : BitVec 12))) = (4294967296 : BitVec 64) := by decide
  have symbolic := (show «dfn'ANDI» (7,1,2048) (fixture s 4294967297) = (let t := fixture s 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 7 ((4294967297 : BitVec 64) &&& (BitVec.signExtend 64 (2048 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ANDI_6_0
example (s : riscv_state) : «dfn'ANDI» (0,0,4095) (fixture s 17) =
 (let t := fixture s 17; t) := by
  rfl

-- immediate_alu_ANDI_6_1
example (s : riscv_state) : «dfn'ANDI» (1,0,4095) (fixture s 17) =
 (let t := fixture s 17; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) &&& (BitVec.signExtend 64 (4095 : BitVec 12))) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'ANDI» (1,0,4095) (fixture s 17) = (let t := fixture s 17; {t with c_gpr := holUpdate 7 (holUpdate 1 ((0 : BitVec 64) &&& (BitVec.signExtend 64 (4095 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ANDI_6_7
example (s : riscv_state) : «dfn'ANDI» (7,0,4095) (fixture s 17) =
 (let t := fixture s 17; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) &&& (BitVec.signExtend 64 (4095 : BitVec 12))) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'ANDI» (7,0,4095) (fixture s 17) = (let t := fixture s 17; {t with c_gpr := holUpdate 7 (holUpdate 7 ((0 : BitVec 64) &&& (BitVec.signExtend 64 (4095 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ANDI_7_0
example (s : riscv_state) : «dfn'ANDI» (0,0,2048) (fixture s 18446744073709551615) =
 (let t := fixture s 18446744073709551615; t) := by
  rfl

-- immediate_alu_ANDI_7_1
example (s : riscv_state) : «dfn'ANDI» (1,0,2048) (fixture s 18446744073709551615) =
 (let t := fixture s 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) &&& (BitVec.signExtend 64 (2048 : BitVec 12))) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'ANDI» (1,0,2048) (fixture s 18446744073709551615) = (let t := fixture s 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 ((0 : BitVec 64) &&& (BitVec.signExtend 64 (2048 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ANDI_7_7
example (s : riscv_state) : «dfn'ANDI» (7,0,2048) (fixture s 18446744073709551615) =
 (let t := fixture s 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) &&& (BitVec.signExtend 64 (2048 : BitVec 12))) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'ANDI» (7,0,2048) (fixture s 18446744073709551615) = (let t := fixture s 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 ((0 : BitVec 64) &&& (BitVec.signExtend 64 (2048 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ANDI_8_0
example (s : riscv_state) : «dfn'ANDI» (0,1,4095) (fixture s 18446744073709551615) =
 (let t := fixture s 18446744073709551615; t) := by
  rfl

-- immediate_alu_ANDI_8_1
example (s : riscv_state) : «dfn'ANDI» (1,1,4095) (fixture s 18446744073709551615) =
 (let t := fixture s 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((18446744073709551615 : BitVec 64) &&& (BitVec.signExtend 64 (4095 : BitVec 12))) = (18446744073709551615 : BitVec 64) := by decide
  have symbolic := (show «dfn'ANDI» (1,1,4095) (fixture s 18446744073709551615) = (let t := fixture s 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 ((18446744073709551615 : BitVec 64) &&& (BitVec.signExtend 64 (4095 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ANDI_8_7
example (s : riscv_state) : «dfn'ANDI» (7,1,4095) (fixture s 18446744073709551615) =
 (let t := fixture s 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((18446744073709551615 : BitVec 64) &&& (BitVec.signExtend 64 (4095 : BitVec 12))) = (18446744073709551615 : BitVec 64) := by decide
  have symbolic := (show «dfn'ANDI» (7,1,4095) (fixture s 18446744073709551615) = (let t := fixture s 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 ((18446744073709551615 : BitVec 64) &&& (BitVec.signExtend 64 (4095 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ANDI_9_0
example (s : riscv_state) : «dfn'ANDI» (0,1,1) (fixture s 2147483648) =
 (let t := fixture s 2147483648; t) := by
  rfl

-- immediate_alu_ANDI_9_1
example (s : riscv_state) : «dfn'ANDI» (1,1,1) (fixture s 2147483648) =
 (let t := fixture s 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((2147483648 : BitVec 64) &&& (BitVec.signExtend 64 (1 : BitVec 12))) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'ANDI» (1,1,1) (fixture s 2147483648) = (let t := fixture s 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 1 ((2147483648 : BitVec 64) &&& (BitVec.signExtend 64 (1 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ANDI_9_7
example (s : riscv_state) : «dfn'ANDI» (7,1,1) (fixture s 2147483648) =
 (let t := fixture s 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((2147483648 : BitVec 64) &&& (BitVec.signExtend 64 (1 : BitVec 12))) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'ANDI» (7,1,1) (fixture s 2147483648) = (let t := fixture s 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 7 ((2147483648 : BitVec 64) &&& (BitVec.signExtend 64 (1 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ORI_0_0
example (s : riscv_state) : «dfn'ORI» (0,1,0) (fixture s 0) =
 (let t := fixture s 0; t) := by
  rfl

-- immediate_alu_ORI_0_1
example (s : riscv_state) : «dfn'ORI» (1,1,0) (fixture s 0) =
 (let t := fixture s 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) ||| (BitVec.signExtend 64 (0 : BitVec 12))) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'ORI» (1,1,0) (fixture s 0) = (let t := fixture s 0; {t with c_gpr := holUpdate 7 (holUpdate 1 ((0 : BitVec 64) ||| (BitVec.signExtend 64 (0 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ORI_0_7
example (s : riscv_state) : «dfn'ORI» (7,1,0) (fixture s 0) =
 (let t := fixture s 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) ||| (BitVec.signExtend 64 (0 : BitVec 12))) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'ORI» (7,1,0) (fixture s 0) = (let t := fixture s 0; {t with c_gpr := holUpdate 7 (holUpdate 7 ((0 : BitVec 64) ||| (BitVec.signExtend 64 (0 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ORI_1_0
example (s : riscv_state) : «dfn'ORI» (0,1,1) (fixture s 18446744073709551615) =
 (let t := fixture s 18446744073709551615; t) := by
  rfl

-- immediate_alu_ORI_1_1
example (s : riscv_state) : «dfn'ORI» (1,1,1) (fixture s 18446744073709551615) =
 (let t := fixture s 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((18446744073709551615 : BitVec 64) ||| (BitVec.signExtend 64 (1 : BitVec 12))) = (18446744073709551615 : BitVec 64) := by decide
  have symbolic := (show «dfn'ORI» (1,1,1) (fixture s 18446744073709551615) = (let t := fixture s 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 ((18446744073709551615 : BitVec 64) ||| (BitVec.signExtend 64 (1 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ORI_1_7
example (s : riscv_state) : «dfn'ORI» (7,1,1) (fixture s 18446744073709551615) =
 (let t := fixture s 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((18446744073709551615 : BitVec 64) ||| (BitVec.signExtend 64 (1 : BitVec 12))) = (18446744073709551615 : BitVec 64) := by decide
  have symbolic := (show «dfn'ORI» (7,1,1) (fixture s 18446744073709551615) = (let t := fixture s 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 ((18446744073709551615 : BitVec 64) ||| (BitVec.signExtend 64 (1 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ORI_2_0
example (s : riscv_state) : «dfn'ORI» (0,1,4095) (fixture s 0) =
 (let t := fixture s 0; t) := by
  rfl

-- immediate_alu_ORI_2_1
example (s : riscv_state) : «dfn'ORI» (1,1,4095) (fixture s 0) =
 (let t := fixture s 0; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) ||| (BitVec.signExtend 64 (4095 : BitVec 12))) = (18446744073709551615 : BitVec 64) := by decide
  have symbolic := (show «dfn'ORI» (1,1,4095) (fixture s 0) = (let t := fixture s 0; {t with c_gpr := holUpdate 7 (holUpdate 1 ((0 : BitVec 64) ||| (BitVec.signExtend 64 (4095 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ORI_2_7
example (s : riscv_state) : «dfn'ORI» (7,1,4095) (fixture s 0) =
 (let t := fixture s 0; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) ||| (BitVec.signExtend 64 (4095 : BitVec 12))) = (18446744073709551615 : BitVec 64) := by decide
  have symbolic := (show «dfn'ORI» (7,1,4095) (fixture s 0) = (let t := fixture s 0; {t with c_gpr := holUpdate 7 (holUpdate 7 ((0 : BitVec 64) ||| (BitVec.signExtend 64 (4095 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ORI_3_0
example (s : riscv_state) : «dfn'ORI» (0,1,2048) (fixture s 9223372036854775808) =
 (let t := fixture s 9223372036854775808; t) := by
  rfl

-- immediate_alu_ORI_3_1
example (s : riscv_state) : «dfn'ORI» (1,1,2048) (fixture s 9223372036854775808) =
 (let t := fixture s 9223372036854775808; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709549568 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((9223372036854775808 : BitVec 64) ||| (BitVec.signExtend 64 (2048 : BitVec 12))) = (18446744073709549568 : BitVec 64) := by decide
  have symbolic := (show «dfn'ORI» (1,1,2048) (fixture s 9223372036854775808) = (let t := fixture s 9223372036854775808; {t with c_gpr := holUpdate 7 (holUpdate 1 ((9223372036854775808 : BitVec 64) ||| (BitVec.signExtend 64 (2048 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ORI_3_7
example (s : riscv_state) : «dfn'ORI» (7,1,2048) (fixture s 9223372036854775808) =
 (let t := fixture s 9223372036854775808; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709549568 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((9223372036854775808 : BitVec 64) ||| (BitVec.signExtend 64 (2048 : BitVec 12))) = (18446744073709549568 : BitVec 64) := by decide
  have symbolic := (show «dfn'ORI» (7,1,2048) (fixture s 9223372036854775808) = (let t := fixture s 9223372036854775808; {t with c_gpr := holUpdate 7 (holUpdate 7 ((9223372036854775808 : BitVec 64) ||| (BitVec.signExtend 64 (2048 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ORI_4_0
example (s : riscv_state) : «dfn'ORI» (0,1,2047) (fixture s 12297829382473034410) =
 (let t := fixture s 12297829382473034410; t) := by
  rfl

-- immediate_alu_ORI_4_1
example (s : riscv_state) : «dfn'ORI» (1,1,2047) (fixture s 12297829382473034410) =
 (let t := fixture s 12297829382473034410; {t with c_gpr := holUpdate 7 (holUpdate 1 12297829382473035775 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((12297829382473034410 : BitVec 64) ||| (BitVec.signExtend 64 (2047 : BitVec 12))) = (12297829382473035775 : BitVec 64) := by decide
  have symbolic := (show «dfn'ORI» (1,1,2047) (fixture s 12297829382473034410) = (let t := fixture s 12297829382473034410; {t with c_gpr := holUpdate 7 (holUpdate 1 ((12297829382473034410 : BitVec 64) ||| (BitVec.signExtend 64 (2047 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ORI_4_7
example (s : riscv_state) : «dfn'ORI» (7,1,2047) (fixture s 12297829382473034410) =
 (let t := fixture s 12297829382473034410; {t with c_gpr := holUpdate 7 (holUpdate 7 12297829382473035775 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((12297829382473034410 : BitVec 64) ||| (BitVec.signExtend 64 (2047 : BitVec 12))) = (12297829382473035775 : BitVec 64) := by decide
  have symbolic := (show «dfn'ORI» (7,1,2047) (fixture s 12297829382473034410) = (let t := fixture s 12297829382473034410; {t with c_gpr := holUpdate 7 (holUpdate 7 ((12297829382473034410 : BitVec 64) ||| (BitVec.signExtend 64 (2047 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ORI_5_0
example (s : riscv_state) : «dfn'ORI» (0,1,2048) (fixture s 4294967297) =
 (let t := fixture s 4294967297; t) := by
  rfl

-- immediate_alu_ORI_5_1
example (s : riscv_state) : «dfn'ORI» (1,1,2048) (fixture s 4294967297) =
 (let t := fixture s 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709549569 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((4294967297 : BitVec 64) ||| (BitVec.signExtend 64 (2048 : BitVec 12))) = (18446744073709549569 : BitVec 64) := by decide
  have symbolic := (show «dfn'ORI» (1,1,2048) (fixture s 4294967297) = (let t := fixture s 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 1 ((4294967297 : BitVec 64) ||| (BitVec.signExtend 64 (2048 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ORI_5_7
example (s : riscv_state) : «dfn'ORI» (7,1,2048) (fixture s 4294967297) =
 (let t := fixture s 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709549569 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((4294967297 : BitVec 64) ||| (BitVec.signExtend 64 (2048 : BitVec 12))) = (18446744073709549569 : BitVec 64) := by decide
  have symbolic := (show «dfn'ORI» (7,1,2048) (fixture s 4294967297) = (let t := fixture s 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 7 ((4294967297 : BitVec 64) ||| (BitVec.signExtend 64 (2048 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ORI_6_0
example (s : riscv_state) : «dfn'ORI» (0,0,4095) (fixture s 17) =
 (let t := fixture s 17; t) := by
  rfl

-- immediate_alu_ORI_6_1
example (s : riscv_state) : «dfn'ORI» (1,0,4095) (fixture s 17) =
 (let t := fixture s 17; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) ||| (BitVec.signExtend 64 (4095 : BitVec 12))) = (18446744073709551615 : BitVec 64) := by decide
  have symbolic := (show «dfn'ORI» (1,0,4095) (fixture s 17) = (let t := fixture s 17; {t with c_gpr := holUpdate 7 (holUpdate 1 ((0 : BitVec 64) ||| (BitVec.signExtend 64 (4095 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ORI_6_7
example (s : riscv_state) : «dfn'ORI» (7,0,4095) (fixture s 17) =
 (let t := fixture s 17; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) ||| (BitVec.signExtend 64 (4095 : BitVec 12))) = (18446744073709551615 : BitVec 64) := by decide
  have symbolic := (show «dfn'ORI» (7,0,4095) (fixture s 17) = (let t := fixture s 17; {t with c_gpr := holUpdate 7 (holUpdate 7 ((0 : BitVec 64) ||| (BitVec.signExtend 64 (4095 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ORI_7_0
example (s : riscv_state) : «dfn'ORI» (0,0,2048) (fixture s 18446744073709551615) =
 (let t := fixture s 18446744073709551615; t) := by
  rfl

-- immediate_alu_ORI_7_1
example (s : riscv_state) : «dfn'ORI» (1,0,2048) (fixture s 18446744073709551615) =
 (let t := fixture s 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709549568 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) ||| (BitVec.signExtend 64 (2048 : BitVec 12))) = (18446744073709549568 : BitVec 64) := by decide
  have symbolic := (show «dfn'ORI» (1,0,2048) (fixture s 18446744073709551615) = (let t := fixture s 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 ((0 : BitVec 64) ||| (BitVec.signExtend 64 (2048 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ORI_7_7
example (s : riscv_state) : «dfn'ORI» (7,0,2048) (fixture s 18446744073709551615) =
 (let t := fixture s 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709549568 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) ||| (BitVec.signExtend 64 (2048 : BitVec 12))) = (18446744073709549568 : BitVec 64) := by decide
  have symbolic := (show «dfn'ORI» (7,0,2048) (fixture s 18446744073709551615) = (let t := fixture s 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 ((0 : BitVec 64) ||| (BitVec.signExtend 64 (2048 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ORI_8_0
example (s : riscv_state) : «dfn'ORI» (0,1,4095) (fixture s 18446744073709551615) =
 (let t := fixture s 18446744073709551615; t) := by
  rfl

-- immediate_alu_ORI_8_1
example (s : riscv_state) : «dfn'ORI» (1,1,4095) (fixture s 18446744073709551615) =
 (let t := fixture s 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((18446744073709551615 : BitVec 64) ||| (BitVec.signExtend 64 (4095 : BitVec 12))) = (18446744073709551615 : BitVec 64) := by decide
  have symbolic := (show «dfn'ORI» (1,1,4095) (fixture s 18446744073709551615) = (let t := fixture s 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 ((18446744073709551615 : BitVec 64) ||| (BitVec.signExtend 64 (4095 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ORI_8_7
example (s : riscv_state) : «dfn'ORI» (7,1,4095) (fixture s 18446744073709551615) =
 (let t := fixture s 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((18446744073709551615 : BitVec 64) ||| (BitVec.signExtend 64 (4095 : BitVec 12))) = (18446744073709551615 : BitVec 64) := by decide
  have symbolic := (show «dfn'ORI» (7,1,4095) (fixture s 18446744073709551615) = (let t := fixture s 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 ((18446744073709551615 : BitVec 64) ||| (BitVec.signExtend 64 (4095 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ORI_9_0
example (s : riscv_state) : «dfn'ORI» (0,1,1) (fixture s 2147483648) =
 (let t := fixture s 2147483648; t) := by
  rfl

-- immediate_alu_ORI_9_1
example (s : riscv_state) : «dfn'ORI» (1,1,1) (fixture s 2147483648) =
 (let t := fixture s 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 1 2147483649 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((2147483648 : BitVec 64) ||| (BitVec.signExtend 64 (1 : BitVec 12))) = (2147483649 : BitVec 64) := by decide
  have symbolic := (show «dfn'ORI» (1,1,1) (fixture s 2147483648) = (let t := fixture s 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 1 ((2147483648 : BitVec 64) ||| (BitVec.signExtend 64 (1 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_ORI_9_7
example (s : riscv_state) : «dfn'ORI» (7,1,1) (fixture s 2147483648) =
 (let t := fixture s 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 7 2147483649 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((2147483648 : BitVec 64) ||| (BitVec.signExtend 64 (1 : BitVec 12))) = (2147483649 : BitVec 64) := by decide
  have symbolic := (show «dfn'ORI» (7,1,1) (fixture s 2147483648) = (let t := fixture s 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 7 ((2147483648 : BitVec 64) ||| (BitVec.signExtend 64 (1 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_XORI_0_0
example (s : riscv_state) : «dfn'XORI» (0,1,0) (fixture s 0) =
 (let t := fixture s 0; t) := by
  rfl

-- immediate_alu_XORI_0_1
example (s : riscv_state) : «dfn'XORI» (1,1,0) (fixture s 0) =
 (let t := fixture s 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) ^^^ (BitVec.signExtend 64 (0 : BitVec 12))) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'XORI» (1,1,0) (fixture s 0) = (let t := fixture s 0; {t with c_gpr := holUpdate 7 (holUpdate 1 ((0 : BitVec 64) ^^^ (BitVec.signExtend 64 (0 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_XORI_0_7
example (s : riscv_state) : «dfn'XORI» (7,1,0) (fixture s 0) =
 (let t := fixture s 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) ^^^ (BitVec.signExtend 64 (0 : BitVec 12))) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'XORI» (7,1,0) (fixture s 0) = (let t := fixture s 0; {t with c_gpr := holUpdate 7 (holUpdate 7 ((0 : BitVec 64) ^^^ (BitVec.signExtend 64 (0 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_XORI_1_0
example (s : riscv_state) : «dfn'XORI» (0,1,1) (fixture s 18446744073709551615) =
 (let t := fixture s 18446744073709551615; t) := by
  rfl

-- immediate_alu_XORI_1_1
example (s : riscv_state) : «dfn'XORI» (1,1,1) (fixture s 18446744073709551615) =
 (let t := fixture s 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((18446744073709551615 : BitVec 64) ^^^ (BitVec.signExtend 64 (1 : BitVec 12))) = (18446744073709551614 : BitVec 64) := by decide
  have symbolic := (show «dfn'XORI» (1,1,1) (fixture s 18446744073709551615) = (let t := fixture s 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 ((18446744073709551615 : BitVec 64) ^^^ (BitVec.signExtend 64 (1 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_XORI_1_7
example (s : riscv_state) : «dfn'XORI» (7,1,1) (fixture s 18446744073709551615) =
 (let t := fixture s 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((18446744073709551615 : BitVec 64) ^^^ (BitVec.signExtend 64 (1 : BitVec 12))) = (18446744073709551614 : BitVec 64) := by decide
  have symbolic := (show «dfn'XORI» (7,1,1) (fixture s 18446744073709551615) = (let t := fixture s 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 ((18446744073709551615 : BitVec 64) ^^^ (BitVec.signExtend 64 (1 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_XORI_2_0
example (s : riscv_state) : «dfn'XORI» (0,1,4095) (fixture s 0) =
 (let t := fixture s 0; t) := by
  rfl

-- immediate_alu_XORI_2_1
example (s : riscv_state) : «dfn'XORI» (1,1,4095) (fixture s 0) =
 (let t := fixture s 0; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) ^^^ (BitVec.signExtend 64 (4095 : BitVec 12))) = (18446744073709551615 : BitVec 64) := by decide
  have symbolic := (show «dfn'XORI» (1,1,4095) (fixture s 0) = (let t := fixture s 0; {t with c_gpr := holUpdate 7 (holUpdate 1 ((0 : BitVec 64) ^^^ (BitVec.signExtend 64 (4095 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_XORI_2_7
example (s : riscv_state) : «dfn'XORI» (7,1,4095) (fixture s 0) =
 (let t := fixture s 0; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) ^^^ (BitVec.signExtend 64 (4095 : BitVec 12))) = (18446744073709551615 : BitVec 64) := by decide
  have symbolic := (show «dfn'XORI» (7,1,4095) (fixture s 0) = (let t := fixture s 0; {t with c_gpr := holUpdate 7 (holUpdate 7 ((0 : BitVec 64) ^^^ (BitVec.signExtend 64 (4095 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_XORI_3_0
example (s : riscv_state) : «dfn'XORI» (0,1,2048) (fixture s 9223372036854775808) =
 (let t := fixture s 9223372036854775808; t) := by
  rfl

-- immediate_alu_XORI_3_1
example (s : riscv_state) : «dfn'XORI» (1,1,2048) (fixture s 9223372036854775808) =
 (let t := fixture s 9223372036854775808; {t with c_gpr := holUpdate 7 (holUpdate 1 9223372036854773760 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((9223372036854775808 : BitVec 64) ^^^ (BitVec.signExtend 64 (2048 : BitVec 12))) = (9223372036854773760 : BitVec 64) := by decide
  have symbolic := (show «dfn'XORI» (1,1,2048) (fixture s 9223372036854775808) = (let t := fixture s 9223372036854775808; {t with c_gpr := holUpdate 7 (holUpdate 1 ((9223372036854775808 : BitVec 64) ^^^ (BitVec.signExtend 64 (2048 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_XORI_3_7
example (s : riscv_state) : «dfn'XORI» (7,1,2048) (fixture s 9223372036854775808) =
 (let t := fixture s 9223372036854775808; {t with c_gpr := holUpdate 7 (holUpdate 7 9223372036854773760 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((9223372036854775808 : BitVec 64) ^^^ (BitVec.signExtend 64 (2048 : BitVec 12))) = (9223372036854773760 : BitVec 64) := by decide
  have symbolic := (show «dfn'XORI» (7,1,2048) (fixture s 9223372036854775808) = (let t := fixture s 9223372036854775808; {t with c_gpr := holUpdate 7 (holUpdate 7 ((9223372036854775808 : BitVec 64) ^^^ (BitVec.signExtend 64 (2048 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_XORI_4_0
example (s : riscv_state) : «dfn'XORI» (0,1,2047) (fixture s 12297829382473034410) =
 (let t := fixture s 12297829382473034410; t) := by
  rfl

-- immediate_alu_XORI_4_1
example (s : riscv_state) : «dfn'XORI» (1,1,2047) (fixture s 12297829382473034410) =
 (let t := fixture s 12297829382473034410; {t with c_gpr := holUpdate 7 (holUpdate 1 12297829382473035093 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((12297829382473034410 : BitVec 64) ^^^ (BitVec.signExtend 64 (2047 : BitVec 12))) = (12297829382473035093 : BitVec 64) := by decide
  have symbolic := (show «dfn'XORI» (1,1,2047) (fixture s 12297829382473034410) = (let t := fixture s 12297829382473034410; {t with c_gpr := holUpdate 7 (holUpdate 1 ((12297829382473034410 : BitVec 64) ^^^ (BitVec.signExtend 64 (2047 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_XORI_4_7
example (s : riscv_state) : «dfn'XORI» (7,1,2047) (fixture s 12297829382473034410) =
 (let t := fixture s 12297829382473034410; {t with c_gpr := holUpdate 7 (holUpdate 7 12297829382473035093 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((12297829382473034410 : BitVec 64) ^^^ (BitVec.signExtend 64 (2047 : BitVec 12))) = (12297829382473035093 : BitVec 64) := by decide
  have symbolic := (show «dfn'XORI» (7,1,2047) (fixture s 12297829382473034410) = (let t := fixture s 12297829382473034410; {t with c_gpr := holUpdate 7 (holUpdate 7 ((12297829382473034410 : BitVec 64) ^^^ (BitVec.signExtend 64 (2047 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_XORI_5_0
example (s : riscv_state) : «dfn'XORI» (0,1,2048) (fixture s 4294967297) =
 (let t := fixture s 4294967297; t) := by
  rfl

-- immediate_alu_XORI_5_1
example (s : riscv_state) : «dfn'XORI» (1,1,2048) (fixture s 4294967297) =
 (let t := fixture s 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744069414582273 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((4294967297 : BitVec 64) ^^^ (BitVec.signExtend 64 (2048 : BitVec 12))) = (18446744069414582273 : BitVec 64) := by decide
  have symbolic := (show «dfn'XORI» (1,1,2048) (fixture s 4294967297) = (let t := fixture s 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 1 ((4294967297 : BitVec 64) ^^^ (BitVec.signExtend 64 (2048 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_XORI_5_7
example (s : riscv_state) : «dfn'XORI» (7,1,2048) (fixture s 4294967297) =
 (let t := fixture s 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744069414582273 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((4294967297 : BitVec 64) ^^^ (BitVec.signExtend 64 (2048 : BitVec 12))) = (18446744069414582273 : BitVec 64) := by decide
  have symbolic := (show «dfn'XORI» (7,1,2048) (fixture s 4294967297) = (let t := fixture s 4294967297; {t with c_gpr := holUpdate 7 (holUpdate 7 ((4294967297 : BitVec 64) ^^^ (BitVec.signExtend 64 (2048 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_XORI_6_0
example (s : riscv_state) : «dfn'XORI» (0,0,4095) (fixture s 17) =
 (let t := fixture s 17; t) := by
  rfl

-- immediate_alu_XORI_6_1
example (s : riscv_state) : «dfn'XORI» (1,0,4095) (fixture s 17) =
 (let t := fixture s 17; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) ^^^ (BitVec.signExtend 64 (4095 : BitVec 12))) = (18446744073709551615 : BitVec 64) := by decide
  have symbolic := (show «dfn'XORI» (1,0,4095) (fixture s 17) = (let t := fixture s 17; {t with c_gpr := holUpdate 7 (holUpdate 1 ((0 : BitVec 64) ^^^ (BitVec.signExtend 64 (4095 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_XORI_6_7
example (s : riscv_state) : «dfn'XORI» (7,0,4095) (fixture s 17) =
 (let t := fixture s 17; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) ^^^ (BitVec.signExtend 64 (4095 : BitVec 12))) = (18446744073709551615 : BitVec 64) := by decide
  have symbolic := (show «dfn'XORI» (7,0,4095) (fixture s 17) = (let t := fixture s 17; {t with c_gpr := holUpdate 7 (holUpdate 7 ((0 : BitVec 64) ^^^ (BitVec.signExtend 64 (4095 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_XORI_7_0
example (s : riscv_state) : «dfn'XORI» (0,0,2048) (fixture s 18446744073709551615) =
 (let t := fixture s 18446744073709551615; t) := by
  rfl

-- immediate_alu_XORI_7_1
example (s : riscv_state) : «dfn'XORI» (1,0,2048) (fixture s 18446744073709551615) =
 (let t := fixture s 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709549568 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) ^^^ (BitVec.signExtend 64 (2048 : BitVec 12))) = (18446744073709549568 : BitVec 64) := by decide
  have symbolic := (show «dfn'XORI» (1,0,2048) (fixture s 18446744073709551615) = (let t := fixture s 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 ((0 : BitVec 64) ^^^ (BitVec.signExtend 64 (2048 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_XORI_7_7
example (s : riscv_state) : «dfn'XORI» (7,0,2048) (fixture s 18446744073709551615) =
 (let t := fixture s 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709549568 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) ^^^ (BitVec.signExtend 64 (2048 : BitVec 12))) = (18446744073709549568 : BitVec 64) := by decide
  have symbolic := (show «dfn'XORI» (7,0,2048) (fixture s 18446744073709551615) = (let t := fixture s 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 ((0 : BitVec 64) ^^^ (BitVec.signExtend 64 (2048 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_XORI_8_0
example (s : riscv_state) : «dfn'XORI» (0,1,4095) (fixture s 18446744073709551615) =
 (let t := fixture s 18446744073709551615; t) := by
  rfl

-- immediate_alu_XORI_8_1
example (s : riscv_state) : «dfn'XORI» (1,1,4095) (fixture s 18446744073709551615) =
 (let t := fixture s 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((18446744073709551615 : BitVec 64) ^^^ (BitVec.signExtend 64 (4095 : BitVec 12))) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'XORI» (1,1,4095) (fixture s 18446744073709551615) = (let t := fixture s 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 ((18446744073709551615 : BitVec 64) ^^^ (BitVec.signExtend 64 (4095 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_XORI_8_7
example (s : riscv_state) : «dfn'XORI» (7,1,4095) (fixture s 18446744073709551615) =
 (let t := fixture s 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((18446744073709551615 : BitVec 64) ^^^ (BitVec.signExtend 64 (4095 : BitVec 12))) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'XORI» (7,1,4095) (fixture s 18446744073709551615) = (let t := fixture s 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 ((18446744073709551615 : BitVec 64) ^^^ (BitVec.signExtend 64 (4095 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_XORI_9_0
example (s : riscv_state) : «dfn'XORI» (0,1,1) (fixture s 2147483648) =
 (let t := fixture s 2147483648; t) := by
  rfl

-- immediate_alu_XORI_9_1
example (s : riscv_state) : «dfn'XORI» (1,1,1) (fixture s 2147483648) =
 (let t := fixture s 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 1 2147483649 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((2147483648 : BitVec 64) ^^^ (BitVec.signExtend 64 (1 : BitVec 12))) = (2147483649 : BitVec 64) := by decide
  have symbolic := (show «dfn'XORI» (1,1,1) (fixture s 2147483648) = (let t := fixture s 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 1 ((2147483648 : BitVec 64) ^^^ (BitVec.signExtend 64 (1 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- immediate_alu_XORI_9_7
example (s : riscv_state) : «dfn'XORI» (7,1,1) (fixture s 2147483648) =
 (let t := fixture s 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 7 2147483649 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((2147483648 : BitVec 64) ^^^ (BitVec.signExtend 64 (1 : BitVec 12))) = (2147483649 : BitVec 64) := by decide
  have symbolic := (show «dfn'XORI» (7,1,1) (fixture s 2147483648) = (let t := fixture s 2147483648; {t with c_gpr := holUpdate 7 (holUpdate 7 ((2147483648 : BitVec 64) ^^^ (BitVec.signExtend 64 (1 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

end Flapjack.Test.L3ImmediateALUParity
