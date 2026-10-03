import Flapjack.RiscV.L3.Defs.RegisterALU

namespace Flapjack.Test.L3RegisterALUParity
open Flapjack.RiscV.L3
private def fixture (s : riscv_state) (a b : BitVec 64) : riscv_state :=
 {s with procID := 7, c_gpr := fun id r => if r = 1 then a else if r = 2 then b else s.c_gpr id r}

-- register_alu_ADD_0_0
example (s : riscv_state) : «dfn'ADD» (0,1,2) (fixture s 0 0) =
 (let t := fixture s 0 0; t) := by
  rfl

-- register_alu_ADD_0_1
example (s : riscv_state) : «dfn'ADD» (1,1,2) (fixture s 0 0) =
 (let t := fixture s 0 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) + (0 : BitVec 64)) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'ADD» (1,1,2) (fixture s 0 0) = (let t := fixture s 0 0; {t with c_gpr := holUpdate 7 (holUpdate 1 ((0 : BitVec 64) + (0 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_ADD_0_2
example (s : riscv_state) : «dfn'ADD» (2,1,2) (fixture s 0 0) =
 (let t := fixture s 0 0; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) + (0 : BitVec 64)) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'ADD» (2,1,2) (fixture s 0 0) = (let t := fixture s 0 0; {t with c_gpr := holUpdate 7 (holUpdate 2 ((0 : BitVec 64) + (0 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_ADD_0_7
example (s : riscv_state) : «dfn'ADD» (7,1,2) (fixture s 0 0) =
 (let t := fixture s 0 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) + (0 : BitVec 64)) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'ADD» (7,1,2) (fixture s 0 0) = (let t := fixture s 0 0; {t with c_gpr := holUpdate 7 (holUpdate 7 ((0 : BitVec 64) + (0 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_ADD_1_0
example (s : riscv_state) : «dfn'ADD» (0,1,2) (fixture s 18446744073709551615 1) =
 (let t := fixture s 18446744073709551615 1; t) := by
  rfl

-- register_alu_ADD_1_1
example (s : riscv_state) : «dfn'ADD» (1,1,2) (fixture s 18446744073709551615 1) =
 (let t := fixture s 18446744073709551615 1; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((18446744073709551615 : BitVec 64) + (1 : BitVec 64)) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'ADD» (1,1,2) (fixture s 18446744073709551615 1) = (let t := fixture s 18446744073709551615 1; {t with c_gpr := holUpdate 7 (holUpdate 1 ((18446744073709551615 : BitVec 64) + (1 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_ADD_1_2
example (s : riscv_state) : «dfn'ADD» (2,1,2) (fixture s 18446744073709551615 1) =
 (let t := fixture s 18446744073709551615 1; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((18446744073709551615 : BitVec 64) + (1 : BitVec 64)) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'ADD» (2,1,2) (fixture s 18446744073709551615 1) = (let t := fixture s 18446744073709551615 1; {t with c_gpr := holUpdate 7 (holUpdate 2 ((18446744073709551615 : BitVec 64) + (1 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_ADD_1_7
example (s : riscv_state) : «dfn'ADD» (7,1,2) (fixture s 18446744073709551615 1) =
 (let t := fixture s 18446744073709551615 1; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((18446744073709551615 : BitVec 64) + (1 : BitVec 64)) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'ADD» (7,1,2) (fixture s 18446744073709551615 1) = (let t := fixture s 18446744073709551615 1; {t with c_gpr := holUpdate 7 (holUpdate 7 ((18446744073709551615 : BitVec 64) + (1 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_ADD_2_0
example (s : riscv_state) : «dfn'ADD» (0,1,2) (fixture s 0 1) =
 (let t := fixture s 0 1; t) := by
  rfl

-- register_alu_ADD_2_1
example (s : riscv_state) : «dfn'ADD» (1,1,2) (fixture s 0 1) =
 (let t := fixture s 0 1; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) + (1 : BitVec 64)) = (1 : BitVec 64) := by decide
  have symbolic := (show «dfn'ADD» (1,1,2) (fixture s 0 1) = (let t := fixture s 0 1; {t with c_gpr := holUpdate 7 (holUpdate 1 ((0 : BitVec 64) + (1 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_ADD_2_2
example (s : riscv_state) : «dfn'ADD» (2,1,2) (fixture s 0 1) =
 (let t := fixture s 0 1; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) + (1 : BitVec 64)) = (1 : BitVec 64) := by decide
  have symbolic := (show «dfn'ADD» (2,1,2) (fixture s 0 1) = (let t := fixture s 0 1; {t with c_gpr := holUpdate 7 (holUpdate 2 ((0 : BitVec 64) + (1 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_ADD_2_7
example (s : riscv_state) : «dfn'ADD» (7,1,2) (fixture s 0 1) =
 (let t := fixture s 0 1; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) + (1 : BitVec 64)) = (1 : BitVec 64) := by decide
  have symbolic := (show «dfn'ADD» (7,1,2) (fixture s 0 1) = (let t := fixture s 0 1; {t with c_gpr := holUpdate 7 (holUpdate 7 ((0 : BitVec 64) + (1 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_ADD_3_0
example (s : riscv_state) : «dfn'ADD» (0,1,2) (fixture s 9223372036854775808 18446744073709551615) =
 (let t := fixture s 9223372036854775808 18446744073709551615; t) := by
  rfl

-- register_alu_ADD_3_1
example (s : riscv_state) : «dfn'ADD» (1,1,2) (fixture s 9223372036854775808 18446744073709551615) =
 (let t := fixture s 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 9223372036854775807 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((9223372036854775808 : BitVec 64) + (18446744073709551615 : BitVec 64)) = (9223372036854775807 : BitVec 64) := by decide
  have symbolic := (show «dfn'ADD» (1,1,2) (fixture s 9223372036854775808 18446744073709551615) = (let t := fixture s 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 ((9223372036854775808 : BitVec 64) + (18446744073709551615 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_ADD_3_2
example (s : riscv_state) : «dfn'ADD» (2,1,2) (fixture s 9223372036854775808 18446744073709551615) =
 (let t := fixture s 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 9223372036854775807 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((9223372036854775808 : BitVec 64) + (18446744073709551615 : BitVec 64)) = (9223372036854775807 : BitVec 64) := by decide
  have symbolic := (show «dfn'ADD» (2,1,2) (fixture s 9223372036854775808 18446744073709551615) = (let t := fixture s 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 ((9223372036854775808 : BitVec 64) + (18446744073709551615 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_ADD_3_7
example (s : riscv_state) : «dfn'ADD» (7,1,2) (fixture s 9223372036854775808 18446744073709551615) =
 (let t := fixture s 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 9223372036854775807 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((9223372036854775808 : BitVec 64) + (18446744073709551615 : BitVec 64)) = (9223372036854775807 : BitVec 64) := by decide
  have symbolic := (show «dfn'ADD» (7,1,2) (fixture s 9223372036854775808 18446744073709551615) = (let t := fixture s 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 ((9223372036854775808 : BitVec 64) + (18446744073709551615 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_ADD_4_0
example (s : riscv_state) : «dfn'ADD» (0,1,2) (fixture s 12297829382473034410 6148914691236517205) =
 (let t := fixture s 12297829382473034410 6148914691236517205; t) := by
  rfl

-- register_alu_ADD_4_1
example (s : riscv_state) : «dfn'ADD» (1,1,2) (fixture s 12297829382473034410 6148914691236517205) =
 (let t := fixture s 12297829382473034410 6148914691236517205; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((12297829382473034410 : BitVec 64) + (6148914691236517205 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
  have symbolic := (show «dfn'ADD» (1,1,2) (fixture s 12297829382473034410 6148914691236517205) = (let t := fixture s 12297829382473034410 6148914691236517205; {t with c_gpr := holUpdate 7 (holUpdate 1 ((12297829382473034410 : BitVec 64) + (6148914691236517205 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_ADD_4_2
example (s : riscv_state) : «dfn'ADD» (2,1,2) (fixture s 12297829382473034410 6148914691236517205) =
 (let t := fixture s 12297829382473034410 6148914691236517205; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((12297829382473034410 : BitVec 64) + (6148914691236517205 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
  have symbolic := (show «dfn'ADD» (2,1,2) (fixture s 12297829382473034410 6148914691236517205) = (let t := fixture s 12297829382473034410 6148914691236517205; {t with c_gpr := holUpdate 7 (holUpdate 2 ((12297829382473034410 : BitVec 64) + (6148914691236517205 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_ADD_4_7
example (s : riscv_state) : «dfn'ADD» (7,1,2) (fixture s 12297829382473034410 6148914691236517205) =
 (let t := fixture s 12297829382473034410 6148914691236517205; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((12297829382473034410 : BitVec 64) + (6148914691236517205 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
  have symbolic := (show «dfn'ADD» (7,1,2) (fixture s 12297829382473034410 6148914691236517205) = (let t := fixture s 12297829382473034410 6148914691236517205; {t with c_gpr := holUpdate 7 (holUpdate 7 ((12297829382473034410 : BitVec 64) + (6148914691236517205 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_ADD_5_0
example (s : riscv_state) : «dfn'ADD» (0,1,2) (fixture s 4294967297 1) =
 (let t := fixture s 4294967297 1; t) := by
  rfl

-- register_alu_ADD_5_1
example (s : riscv_state) : «dfn'ADD» (1,1,2) (fixture s 4294967297 1) =
 (let t := fixture s 4294967297 1; {t with c_gpr := holUpdate 7 (holUpdate 1 4294967298 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((4294967297 : BitVec 64) + (1 : BitVec 64)) = (4294967298 : BitVec 64) := by decide
  have symbolic := (show «dfn'ADD» (1,1,2) (fixture s 4294967297 1) = (let t := fixture s 4294967297 1; {t with c_gpr := holUpdate 7 (holUpdate 1 ((4294967297 : BitVec 64) + (1 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_ADD_5_2
example (s : riscv_state) : «dfn'ADD» (2,1,2) (fixture s 4294967297 1) =
 (let t := fixture s 4294967297 1; {t with c_gpr := holUpdate 7 (holUpdate 2 4294967298 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((4294967297 : BitVec 64) + (1 : BitVec 64)) = (4294967298 : BitVec 64) := by decide
  have symbolic := (show «dfn'ADD» (2,1,2) (fixture s 4294967297 1) = (let t := fixture s 4294967297 1; {t with c_gpr := holUpdate 7 (holUpdate 2 ((4294967297 : BitVec 64) + (1 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_ADD_5_7
example (s : riscv_state) : «dfn'ADD» (7,1,2) (fixture s 4294967297 1) =
 (let t := fixture s 4294967297 1; {t with c_gpr := holUpdate 7 (holUpdate 7 4294967298 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((4294967297 : BitVec 64) + (1 : BitVec 64)) = (4294967298 : BitVec 64) := by decide
  have symbolic := (show «dfn'ADD» (7,1,2) (fixture s 4294967297 1) = (let t := fixture s 4294967297 1; {t with c_gpr := holUpdate 7 (holUpdate 7 ((4294967297 : BitVec 64) + (1 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_ADD_6_0
example (s : riscv_state) : «dfn'ADD» (0,0,2) (fixture s 18446744073709551615 17) =
 (let t := fixture s 18446744073709551615 17; t) := by
  rfl

-- register_alu_ADD_6_1
example (s : riscv_state) : «dfn'ADD» (1,0,2) (fixture s 18446744073709551615 17) =
 (let t := fixture s 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 1 17 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) + (17 : BitVec 64)) = (17 : BitVec 64) := by decide
  have symbolic := (show «dfn'ADD» (1,0,2) (fixture s 18446744073709551615 17) = (let t := fixture s 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 1 ((0 : BitVec 64) + (17 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_ADD_6_2
example (s : riscv_state) : «dfn'ADD» (2,0,2) (fixture s 18446744073709551615 17) =
 (let t := fixture s 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 2 17 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) + (17 : BitVec 64)) = (17 : BitVec 64) := by decide
  have symbolic := (show «dfn'ADD» (2,0,2) (fixture s 18446744073709551615 17) = (let t := fixture s 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 2 ((0 : BitVec 64) + (17 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_ADD_6_7
example (s : riscv_state) : «dfn'ADD» (7,0,2) (fixture s 18446744073709551615 17) =
 (let t := fixture s 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 7 17 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) + (17 : BitVec 64)) = (17 : BitVec 64) := by decide
  have symbolic := (show «dfn'ADD» (7,0,2) (fixture s 18446744073709551615 17) = (let t := fixture s 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 7 ((0 : BitVec 64) + (17 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_ADD_7_0
example (s : riscv_state) : «dfn'ADD» (0,1,0) (fixture s 17 18446744073709551615) =
 (let t := fixture s 17 18446744073709551615; t) := by
  rfl

-- register_alu_ADD_7_1
example (s : riscv_state) : «dfn'ADD» (1,1,0) (fixture s 17 18446744073709551615) =
 (let t := fixture s 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 17 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((17 : BitVec 64) + (0 : BitVec 64)) = (17 : BitVec 64) := by decide
  have symbolic := (show «dfn'ADD» (1,1,0) (fixture s 17 18446744073709551615) = (let t := fixture s 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 ((17 : BitVec 64) + (0 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_ADD_7_2
example (s : riscv_state) : «dfn'ADD» (2,1,0) (fixture s 17 18446744073709551615) =
 (let t := fixture s 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 17 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((17 : BitVec 64) + (0 : BitVec 64)) = (17 : BitVec 64) := by decide
  have symbolic := (show «dfn'ADD» (2,1,0) (fixture s 17 18446744073709551615) = (let t := fixture s 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 ((17 : BitVec 64) + (0 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_ADD_7_7
example (s : riscv_state) : «dfn'ADD» (7,1,0) (fixture s 17 18446744073709551615) =
 (let t := fixture s 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 17 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((17 : BitVec 64) + (0 : BitVec 64)) = (17 : BitVec 64) := by decide
  have symbolic := (show «dfn'ADD» (7,1,0) (fixture s 17 18446744073709551615) = (let t := fixture s 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 ((17 : BitVec 64) + (0 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_SUB_0_0
example (s : riscv_state) : «dfn'SUB» (0,1,2) (fixture s 0 0) =
 (let t := fixture s 0 0; t) := by
  rfl

-- register_alu_SUB_0_1
example (s : riscv_state) : «dfn'SUB» (1,1,2) (fixture s 0 0) =
 (let t := fixture s 0 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) - (0 : BitVec 64)) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'SUB» (1,1,2) (fixture s 0 0) = (let t := fixture s 0 0; {t with c_gpr := holUpdate 7 (holUpdate 1 ((0 : BitVec 64) - (0 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_SUB_0_2
example (s : riscv_state) : «dfn'SUB» (2,1,2) (fixture s 0 0) =
 (let t := fixture s 0 0; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) - (0 : BitVec 64)) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'SUB» (2,1,2) (fixture s 0 0) = (let t := fixture s 0 0; {t with c_gpr := holUpdate 7 (holUpdate 2 ((0 : BitVec 64) - (0 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_SUB_0_7
example (s : riscv_state) : «dfn'SUB» (7,1,2) (fixture s 0 0) =
 (let t := fixture s 0 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) - (0 : BitVec 64)) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'SUB» (7,1,2) (fixture s 0 0) = (let t := fixture s 0 0; {t with c_gpr := holUpdate 7 (holUpdate 7 ((0 : BitVec 64) - (0 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_SUB_1_0
example (s : riscv_state) : «dfn'SUB» (0,1,2) (fixture s 18446744073709551615 1) =
 (let t := fixture s 18446744073709551615 1; t) := by
  rfl

-- register_alu_SUB_1_1
example (s : riscv_state) : «dfn'SUB» (1,1,2) (fixture s 18446744073709551615 1) =
 (let t := fixture s 18446744073709551615 1; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((18446744073709551615 : BitVec 64) - (1 : BitVec 64)) = (18446744073709551614 : BitVec 64) := by decide
  have symbolic := (show «dfn'SUB» (1,1,2) (fixture s 18446744073709551615 1) = (let t := fixture s 18446744073709551615 1; {t with c_gpr := holUpdate 7 (holUpdate 1 ((18446744073709551615 : BitVec 64) - (1 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_SUB_1_2
example (s : riscv_state) : «dfn'SUB» (2,1,2) (fixture s 18446744073709551615 1) =
 (let t := fixture s 18446744073709551615 1; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((18446744073709551615 : BitVec 64) - (1 : BitVec 64)) = (18446744073709551614 : BitVec 64) := by decide
  have symbolic := (show «dfn'SUB» (2,1,2) (fixture s 18446744073709551615 1) = (let t := fixture s 18446744073709551615 1; {t with c_gpr := holUpdate 7 (holUpdate 2 ((18446744073709551615 : BitVec 64) - (1 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_SUB_1_7
example (s : riscv_state) : «dfn'SUB» (7,1,2) (fixture s 18446744073709551615 1) =
 (let t := fixture s 18446744073709551615 1; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((18446744073709551615 : BitVec 64) - (1 : BitVec 64)) = (18446744073709551614 : BitVec 64) := by decide
  have symbolic := (show «dfn'SUB» (7,1,2) (fixture s 18446744073709551615 1) = (let t := fixture s 18446744073709551615 1; {t with c_gpr := holUpdate 7 (holUpdate 7 ((18446744073709551615 : BitVec 64) - (1 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_SUB_2_0
example (s : riscv_state) : «dfn'SUB» (0,1,2) (fixture s 0 1) =
 (let t := fixture s 0 1; t) := by
  rfl

-- register_alu_SUB_2_1
example (s : riscv_state) : «dfn'SUB» (1,1,2) (fixture s 0 1) =
 (let t := fixture s 0 1; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) - (1 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
  have symbolic := (show «dfn'SUB» (1,1,2) (fixture s 0 1) = (let t := fixture s 0 1; {t with c_gpr := holUpdate 7 (holUpdate 1 ((0 : BitVec 64) - (1 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_SUB_2_2
example (s : riscv_state) : «dfn'SUB» (2,1,2) (fixture s 0 1) =
 (let t := fixture s 0 1; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) - (1 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
  have symbolic := (show «dfn'SUB» (2,1,2) (fixture s 0 1) = (let t := fixture s 0 1; {t with c_gpr := holUpdate 7 (holUpdate 2 ((0 : BitVec 64) - (1 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_SUB_2_7
example (s : riscv_state) : «dfn'SUB» (7,1,2) (fixture s 0 1) =
 (let t := fixture s 0 1; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) - (1 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
  have symbolic := (show «dfn'SUB» (7,1,2) (fixture s 0 1) = (let t := fixture s 0 1; {t with c_gpr := holUpdate 7 (holUpdate 7 ((0 : BitVec 64) - (1 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_SUB_3_0
example (s : riscv_state) : «dfn'SUB» (0,1,2) (fixture s 9223372036854775808 18446744073709551615) =
 (let t := fixture s 9223372036854775808 18446744073709551615; t) := by
  rfl

-- register_alu_SUB_3_1
example (s : riscv_state) : «dfn'SUB» (1,1,2) (fixture s 9223372036854775808 18446744073709551615) =
 (let t := fixture s 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 9223372036854775809 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((9223372036854775808 : BitVec 64) - (18446744073709551615 : BitVec 64)) = (9223372036854775809 : BitVec 64) := by decide
  have symbolic := (show «dfn'SUB» (1,1,2) (fixture s 9223372036854775808 18446744073709551615) = (let t := fixture s 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 ((9223372036854775808 : BitVec 64) - (18446744073709551615 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_SUB_3_2
example (s : riscv_state) : «dfn'SUB» (2,1,2) (fixture s 9223372036854775808 18446744073709551615) =
 (let t := fixture s 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 9223372036854775809 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((9223372036854775808 : BitVec 64) - (18446744073709551615 : BitVec 64)) = (9223372036854775809 : BitVec 64) := by decide
  have symbolic := (show «dfn'SUB» (2,1,2) (fixture s 9223372036854775808 18446744073709551615) = (let t := fixture s 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 ((9223372036854775808 : BitVec 64) - (18446744073709551615 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_SUB_3_7
example (s : riscv_state) : «dfn'SUB» (7,1,2) (fixture s 9223372036854775808 18446744073709551615) =
 (let t := fixture s 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 9223372036854775809 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((9223372036854775808 : BitVec 64) - (18446744073709551615 : BitVec 64)) = (9223372036854775809 : BitVec 64) := by decide
  have symbolic := (show «dfn'SUB» (7,1,2) (fixture s 9223372036854775808 18446744073709551615) = (let t := fixture s 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 ((9223372036854775808 : BitVec 64) - (18446744073709551615 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_SUB_4_0
example (s : riscv_state) : «dfn'SUB» (0,1,2) (fixture s 12297829382473034410 6148914691236517205) =
 (let t := fixture s 12297829382473034410 6148914691236517205; t) := by
  rfl

-- register_alu_SUB_4_1
example (s : riscv_state) : «dfn'SUB» (1,1,2) (fixture s 12297829382473034410 6148914691236517205) =
 (let t := fixture s 12297829382473034410 6148914691236517205; {t with c_gpr := holUpdate 7 (holUpdate 1 6148914691236517205 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((12297829382473034410 : BitVec 64) - (6148914691236517205 : BitVec 64)) = (6148914691236517205 : BitVec 64) := by decide
  have symbolic := (show «dfn'SUB» (1,1,2) (fixture s 12297829382473034410 6148914691236517205) = (let t := fixture s 12297829382473034410 6148914691236517205; {t with c_gpr := holUpdate 7 (holUpdate 1 ((12297829382473034410 : BitVec 64) - (6148914691236517205 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_SUB_4_2
example (s : riscv_state) : «dfn'SUB» (2,1,2) (fixture s 12297829382473034410 6148914691236517205) =
 (let t := fixture s 12297829382473034410 6148914691236517205; {t with c_gpr := holUpdate 7 (holUpdate 2 6148914691236517205 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((12297829382473034410 : BitVec 64) - (6148914691236517205 : BitVec 64)) = (6148914691236517205 : BitVec 64) := by decide
  have symbolic := (show «dfn'SUB» (2,1,2) (fixture s 12297829382473034410 6148914691236517205) = (let t := fixture s 12297829382473034410 6148914691236517205; {t with c_gpr := holUpdate 7 (holUpdate 2 ((12297829382473034410 : BitVec 64) - (6148914691236517205 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_SUB_4_7
example (s : riscv_state) : «dfn'SUB» (7,1,2) (fixture s 12297829382473034410 6148914691236517205) =
 (let t := fixture s 12297829382473034410 6148914691236517205; {t with c_gpr := holUpdate 7 (holUpdate 7 6148914691236517205 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((12297829382473034410 : BitVec 64) - (6148914691236517205 : BitVec 64)) = (6148914691236517205 : BitVec 64) := by decide
  have symbolic := (show «dfn'SUB» (7,1,2) (fixture s 12297829382473034410 6148914691236517205) = (let t := fixture s 12297829382473034410 6148914691236517205; {t with c_gpr := holUpdate 7 (holUpdate 7 ((12297829382473034410 : BitVec 64) - (6148914691236517205 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_SUB_5_0
example (s : riscv_state) : «dfn'SUB» (0,1,2) (fixture s 4294967297 1) =
 (let t := fixture s 4294967297 1; t) := by
  rfl

-- register_alu_SUB_5_1
example (s : riscv_state) : «dfn'SUB» (1,1,2) (fixture s 4294967297 1) =
 (let t := fixture s 4294967297 1; {t with c_gpr := holUpdate 7 (holUpdate 1 4294967296 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((4294967297 : BitVec 64) - (1 : BitVec 64)) = (4294967296 : BitVec 64) := by decide
  have symbolic := (show «dfn'SUB» (1,1,2) (fixture s 4294967297 1) = (let t := fixture s 4294967297 1; {t with c_gpr := holUpdate 7 (holUpdate 1 ((4294967297 : BitVec 64) - (1 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_SUB_5_2
example (s : riscv_state) : «dfn'SUB» (2,1,2) (fixture s 4294967297 1) =
 (let t := fixture s 4294967297 1; {t with c_gpr := holUpdate 7 (holUpdate 2 4294967296 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((4294967297 : BitVec 64) - (1 : BitVec 64)) = (4294967296 : BitVec 64) := by decide
  have symbolic := (show «dfn'SUB» (2,1,2) (fixture s 4294967297 1) = (let t := fixture s 4294967297 1; {t with c_gpr := holUpdate 7 (holUpdate 2 ((4294967297 : BitVec 64) - (1 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_SUB_5_7
example (s : riscv_state) : «dfn'SUB» (7,1,2) (fixture s 4294967297 1) =
 (let t := fixture s 4294967297 1; {t with c_gpr := holUpdate 7 (holUpdate 7 4294967296 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((4294967297 : BitVec 64) - (1 : BitVec 64)) = (4294967296 : BitVec 64) := by decide
  have symbolic := (show «dfn'SUB» (7,1,2) (fixture s 4294967297 1) = (let t := fixture s 4294967297 1; {t with c_gpr := holUpdate 7 (holUpdate 7 ((4294967297 : BitVec 64) - (1 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_SUB_6_0
example (s : riscv_state) : «dfn'SUB» (0,0,2) (fixture s 18446744073709551615 17) =
 (let t := fixture s 18446744073709551615 17; t) := by
  rfl

-- register_alu_SUB_6_1
example (s : riscv_state) : «dfn'SUB» (1,0,2) (fixture s 18446744073709551615 17) =
 (let t := fixture s 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551599 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) - (17 : BitVec 64)) = (18446744073709551599 : BitVec 64) := by decide
  have symbolic := (show «dfn'SUB» (1,0,2) (fixture s 18446744073709551615 17) = (let t := fixture s 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 1 ((0 : BitVec 64) - (17 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_SUB_6_2
example (s : riscv_state) : «dfn'SUB» (2,0,2) (fixture s 18446744073709551615 17) =
 (let t := fixture s 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551599 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) - (17 : BitVec 64)) = (18446744073709551599 : BitVec 64) := by decide
  have symbolic := (show «dfn'SUB» (2,0,2) (fixture s 18446744073709551615 17) = (let t := fixture s 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 2 ((0 : BitVec 64) - (17 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_SUB_6_7
example (s : riscv_state) : «dfn'SUB» (7,0,2) (fixture s 18446744073709551615 17) =
 (let t := fixture s 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551599 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) - (17 : BitVec 64)) = (18446744073709551599 : BitVec 64) := by decide
  have symbolic := (show «dfn'SUB» (7,0,2) (fixture s 18446744073709551615 17) = (let t := fixture s 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 7 ((0 : BitVec 64) - (17 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_SUB_7_0
example (s : riscv_state) : «dfn'SUB» (0,1,0) (fixture s 17 18446744073709551615) =
 (let t := fixture s 17 18446744073709551615; t) := by
  rfl

-- register_alu_SUB_7_1
example (s : riscv_state) : «dfn'SUB» (1,1,0) (fixture s 17 18446744073709551615) =
 (let t := fixture s 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 17 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((17 : BitVec 64) - (0 : BitVec 64)) = (17 : BitVec 64) := by decide
  have symbolic := (show «dfn'SUB» (1,1,0) (fixture s 17 18446744073709551615) = (let t := fixture s 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 ((17 : BitVec 64) - (0 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_SUB_7_2
example (s : riscv_state) : «dfn'SUB» (2,1,0) (fixture s 17 18446744073709551615) =
 (let t := fixture s 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 17 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((17 : BitVec 64) - (0 : BitVec 64)) = (17 : BitVec 64) := by decide
  have symbolic := (show «dfn'SUB» (2,1,0) (fixture s 17 18446744073709551615) = (let t := fixture s 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 ((17 : BitVec 64) - (0 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_SUB_7_7
example (s : riscv_state) : «dfn'SUB» (7,1,0) (fixture s 17 18446744073709551615) =
 (let t := fixture s 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 17 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((17 : BitVec 64) - (0 : BitVec 64)) = (17 : BitVec 64) := by decide
  have symbolic := (show «dfn'SUB» (7,1,0) (fixture s 17 18446744073709551615) = (let t := fixture s 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 ((17 : BitVec 64) - (0 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_AND_0_0
example (s : riscv_state) : «dfn'AND» (0,1,2) (fixture s 0 0) =
 (let t := fixture s 0 0; t) := by
  rfl

-- register_alu_AND_0_1
example (s : riscv_state) : «dfn'AND» (1,1,2) (fixture s 0 0) =
 (let t := fixture s 0 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) &&& (0 : BitVec 64)) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'AND» (1,1,2) (fixture s 0 0) = (let t := fixture s 0 0; {t with c_gpr := holUpdate 7 (holUpdate 1 ((0 : BitVec 64) &&& (0 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_AND_0_2
example (s : riscv_state) : «dfn'AND» (2,1,2) (fixture s 0 0) =
 (let t := fixture s 0 0; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) &&& (0 : BitVec 64)) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'AND» (2,1,2) (fixture s 0 0) = (let t := fixture s 0 0; {t with c_gpr := holUpdate 7 (holUpdate 2 ((0 : BitVec 64) &&& (0 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_AND_0_7
example (s : riscv_state) : «dfn'AND» (7,1,2) (fixture s 0 0) =
 (let t := fixture s 0 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) &&& (0 : BitVec 64)) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'AND» (7,1,2) (fixture s 0 0) = (let t := fixture s 0 0; {t with c_gpr := holUpdate 7 (holUpdate 7 ((0 : BitVec 64) &&& (0 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_AND_1_0
example (s : riscv_state) : «dfn'AND» (0,1,2) (fixture s 18446744073709551615 1) =
 (let t := fixture s 18446744073709551615 1; t) := by
  rfl

-- register_alu_AND_1_1
example (s : riscv_state) : «dfn'AND» (1,1,2) (fixture s 18446744073709551615 1) =
 (let t := fixture s 18446744073709551615 1; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((18446744073709551615 : BitVec 64) &&& (1 : BitVec 64)) = (1 : BitVec 64) := by decide
  have symbolic := (show «dfn'AND» (1,1,2) (fixture s 18446744073709551615 1) = (let t := fixture s 18446744073709551615 1; {t with c_gpr := holUpdate 7 (holUpdate 1 ((18446744073709551615 : BitVec 64) &&& (1 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_AND_1_2
example (s : riscv_state) : «dfn'AND» (2,1,2) (fixture s 18446744073709551615 1) =
 (let t := fixture s 18446744073709551615 1; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((18446744073709551615 : BitVec 64) &&& (1 : BitVec 64)) = (1 : BitVec 64) := by decide
  have symbolic := (show «dfn'AND» (2,1,2) (fixture s 18446744073709551615 1) = (let t := fixture s 18446744073709551615 1; {t with c_gpr := holUpdate 7 (holUpdate 2 ((18446744073709551615 : BitVec 64) &&& (1 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_AND_1_7
example (s : riscv_state) : «dfn'AND» (7,1,2) (fixture s 18446744073709551615 1) =
 (let t := fixture s 18446744073709551615 1; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((18446744073709551615 : BitVec 64) &&& (1 : BitVec 64)) = (1 : BitVec 64) := by decide
  have symbolic := (show «dfn'AND» (7,1,2) (fixture s 18446744073709551615 1) = (let t := fixture s 18446744073709551615 1; {t with c_gpr := holUpdate 7 (holUpdate 7 ((18446744073709551615 : BitVec 64) &&& (1 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_AND_2_0
example (s : riscv_state) : «dfn'AND» (0,1,2) (fixture s 0 1) =
 (let t := fixture s 0 1; t) := by
  rfl

-- register_alu_AND_2_1
example (s : riscv_state) : «dfn'AND» (1,1,2) (fixture s 0 1) =
 (let t := fixture s 0 1; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) &&& (1 : BitVec 64)) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'AND» (1,1,2) (fixture s 0 1) = (let t := fixture s 0 1; {t with c_gpr := holUpdate 7 (holUpdate 1 ((0 : BitVec 64) &&& (1 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_AND_2_2
example (s : riscv_state) : «dfn'AND» (2,1,2) (fixture s 0 1) =
 (let t := fixture s 0 1; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) &&& (1 : BitVec 64)) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'AND» (2,1,2) (fixture s 0 1) = (let t := fixture s 0 1; {t with c_gpr := holUpdate 7 (holUpdate 2 ((0 : BitVec 64) &&& (1 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_AND_2_7
example (s : riscv_state) : «dfn'AND» (7,1,2) (fixture s 0 1) =
 (let t := fixture s 0 1; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) &&& (1 : BitVec 64)) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'AND» (7,1,2) (fixture s 0 1) = (let t := fixture s 0 1; {t with c_gpr := holUpdate 7 (holUpdate 7 ((0 : BitVec 64) &&& (1 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_AND_3_0
example (s : riscv_state) : «dfn'AND» (0,1,2) (fixture s 9223372036854775808 18446744073709551615) =
 (let t := fixture s 9223372036854775808 18446744073709551615; t) := by
  rfl

-- register_alu_AND_3_1
example (s : riscv_state) : «dfn'AND» (1,1,2) (fixture s 9223372036854775808 18446744073709551615) =
 (let t := fixture s 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((9223372036854775808 : BitVec 64) &&& (18446744073709551615 : BitVec 64)) = (9223372036854775808 : BitVec 64) := by decide
  have symbolic := (show «dfn'AND» (1,1,2) (fixture s 9223372036854775808 18446744073709551615) = (let t := fixture s 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 ((9223372036854775808 : BitVec 64) &&& (18446744073709551615 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_AND_3_2
example (s : riscv_state) : «dfn'AND» (2,1,2) (fixture s 9223372036854775808 18446744073709551615) =
 (let t := fixture s 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((9223372036854775808 : BitVec 64) &&& (18446744073709551615 : BitVec 64)) = (9223372036854775808 : BitVec 64) := by decide
  have symbolic := (show «dfn'AND» (2,1,2) (fixture s 9223372036854775808 18446744073709551615) = (let t := fixture s 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 ((9223372036854775808 : BitVec 64) &&& (18446744073709551615 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_AND_3_7
example (s : riscv_state) : «dfn'AND» (7,1,2) (fixture s 9223372036854775808 18446744073709551615) =
 (let t := fixture s 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((9223372036854775808 : BitVec 64) &&& (18446744073709551615 : BitVec 64)) = (9223372036854775808 : BitVec 64) := by decide
  have symbolic := (show «dfn'AND» (7,1,2) (fixture s 9223372036854775808 18446744073709551615) = (let t := fixture s 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 ((9223372036854775808 : BitVec 64) &&& (18446744073709551615 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_AND_4_0
example (s : riscv_state) : «dfn'AND» (0,1,2) (fixture s 12297829382473034410 6148914691236517205) =
 (let t := fixture s 12297829382473034410 6148914691236517205; t) := by
  rfl

-- register_alu_AND_4_1
example (s : riscv_state) : «dfn'AND» (1,1,2) (fixture s 12297829382473034410 6148914691236517205) =
 (let t := fixture s 12297829382473034410 6148914691236517205; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((12297829382473034410 : BitVec 64) &&& (6148914691236517205 : BitVec 64)) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'AND» (1,1,2) (fixture s 12297829382473034410 6148914691236517205) = (let t := fixture s 12297829382473034410 6148914691236517205; {t with c_gpr := holUpdate 7 (holUpdate 1 ((12297829382473034410 : BitVec 64) &&& (6148914691236517205 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_AND_4_2
example (s : riscv_state) : «dfn'AND» (2,1,2) (fixture s 12297829382473034410 6148914691236517205) =
 (let t := fixture s 12297829382473034410 6148914691236517205; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((12297829382473034410 : BitVec 64) &&& (6148914691236517205 : BitVec 64)) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'AND» (2,1,2) (fixture s 12297829382473034410 6148914691236517205) = (let t := fixture s 12297829382473034410 6148914691236517205; {t with c_gpr := holUpdate 7 (holUpdate 2 ((12297829382473034410 : BitVec 64) &&& (6148914691236517205 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_AND_4_7
example (s : riscv_state) : «dfn'AND» (7,1,2) (fixture s 12297829382473034410 6148914691236517205) =
 (let t := fixture s 12297829382473034410 6148914691236517205; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((12297829382473034410 : BitVec 64) &&& (6148914691236517205 : BitVec 64)) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'AND» (7,1,2) (fixture s 12297829382473034410 6148914691236517205) = (let t := fixture s 12297829382473034410 6148914691236517205; {t with c_gpr := holUpdate 7 (holUpdate 7 ((12297829382473034410 : BitVec 64) &&& (6148914691236517205 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_AND_5_0
example (s : riscv_state) : «dfn'AND» (0,1,2) (fixture s 4294967297 1) =
 (let t := fixture s 4294967297 1; t) := by
  rfl

-- register_alu_AND_5_1
example (s : riscv_state) : «dfn'AND» (1,1,2) (fixture s 4294967297 1) =
 (let t := fixture s 4294967297 1; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((4294967297 : BitVec 64) &&& (1 : BitVec 64)) = (1 : BitVec 64) := by decide
  have symbolic := (show «dfn'AND» (1,1,2) (fixture s 4294967297 1) = (let t := fixture s 4294967297 1; {t with c_gpr := holUpdate 7 (holUpdate 1 ((4294967297 : BitVec 64) &&& (1 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_AND_5_2
example (s : riscv_state) : «dfn'AND» (2,1,2) (fixture s 4294967297 1) =
 (let t := fixture s 4294967297 1; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((4294967297 : BitVec 64) &&& (1 : BitVec 64)) = (1 : BitVec 64) := by decide
  have symbolic := (show «dfn'AND» (2,1,2) (fixture s 4294967297 1) = (let t := fixture s 4294967297 1; {t with c_gpr := holUpdate 7 (holUpdate 2 ((4294967297 : BitVec 64) &&& (1 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_AND_5_7
example (s : riscv_state) : «dfn'AND» (7,1,2) (fixture s 4294967297 1) =
 (let t := fixture s 4294967297 1; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((4294967297 : BitVec 64) &&& (1 : BitVec 64)) = (1 : BitVec 64) := by decide
  have symbolic := (show «dfn'AND» (7,1,2) (fixture s 4294967297 1) = (let t := fixture s 4294967297 1; {t with c_gpr := holUpdate 7 (holUpdate 7 ((4294967297 : BitVec 64) &&& (1 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_AND_6_0
example (s : riscv_state) : «dfn'AND» (0,0,2) (fixture s 18446744073709551615 17) =
 (let t := fixture s 18446744073709551615 17; t) := by
  rfl

-- register_alu_AND_6_1
example (s : riscv_state) : «dfn'AND» (1,0,2) (fixture s 18446744073709551615 17) =
 (let t := fixture s 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) &&& (17 : BitVec 64)) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'AND» (1,0,2) (fixture s 18446744073709551615 17) = (let t := fixture s 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 1 ((0 : BitVec 64) &&& (17 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_AND_6_2
example (s : riscv_state) : «dfn'AND» (2,0,2) (fixture s 18446744073709551615 17) =
 (let t := fixture s 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) &&& (17 : BitVec 64)) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'AND» (2,0,2) (fixture s 18446744073709551615 17) = (let t := fixture s 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 2 ((0 : BitVec 64) &&& (17 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_AND_6_7
example (s : riscv_state) : «dfn'AND» (7,0,2) (fixture s 18446744073709551615 17) =
 (let t := fixture s 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) &&& (17 : BitVec 64)) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'AND» (7,0,2) (fixture s 18446744073709551615 17) = (let t := fixture s 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 7 ((0 : BitVec 64) &&& (17 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_AND_7_0
example (s : riscv_state) : «dfn'AND» (0,1,0) (fixture s 17 18446744073709551615) =
 (let t := fixture s 17 18446744073709551615; t) := by
  rfl

-- register_alu_AND_7_1
example (s : riscv_state) : «dfn'AND» (1,1,0) (fixture s 17 18446744073709551615) =
 (let t := fixture s 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((17 : BitVec 64) &&& (0 : BitVec 64)) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'AND» (1,1,0) (fixture s 17 18446744073709551615) = (let t := fixture s 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 ((17 : BitVec 64) &&& (0 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_AND_7_2
example (s : riscv_state) : «dfn'AND» (2,1,0) (fixture s 17 18446744073709551615) =
 (let t := fixture s 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((17 : BitVec 64) &&& (0 : BitVec 64)) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'AND» (2,1,0) (fixture s 17 18446744073709551615) = (let t := fixture s 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 ((17 : BitVec 64) &&& (0 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_AND_7_7
example (s : riscv_state) : «dfn'AND» (7,1,0) (fixture s 17 18446744073709551615) =
 (let t := fixture s 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((17 : BitVec 64) &&& (0 : BitVec 64)) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'AND» (7,1,0) (fixture s 17 18446744073709551615) = (let t := fixture s 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 ((17 : BitVec 64) &&& (0 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_OR_0_0
example (s : riscv_state) : «dfn'OR» (0,1,2) (fixture s 0 0) =
 (let t := fixture s 0 0; t) := by
  rfl

-- register_alu_OR_0_1
example (s : riscv_state) : «dfn'OR» (1,1,2) (fixture s 0 0) =
 (let t := fixture s 0 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) ||| (0 : BitVec 64)) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'OR» (1,1,2) (fixture s 0 0) = (let t := fixture s 0 0; {t with c_gpr := holUpdate 7 (holUpdate 1 ((0 : BitVec 64) ||| (0 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_OR_0_2
example (s : riscv_state) : «dfn'OR» (2,1,2) (fixture s 0 0) =
 (let t := fixture s 0 0; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) ||| (0 : BitVec 64)) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'OR» (2,1,2) (fixture s 0 0) = (let t := fixture s 0 0; {t with c_gpr := holUpdate 7 (holUpdate 2 ((0 : BitVec 64) ||| (0 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_OR_0_7
example (s : riscv_state) : «dfn'OR» (7,1,2) (fixture s 0 0) =
 (let t := fixture s 0 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) ||| (0 : BitVec 64)) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'OR» (7,1,2) (fixture s 0 0) = (let t := fixture s 0 0; {t with c_gpr := holUpdate 7 (holUpdate 7 ((0 : BitVec 64) ||| (0 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_OR_1_0
example (s : riscv_state) : «dfn'OR» (0,1,2) (fixture s 18446744073709551615 1) =
 (let t := fixture s 18446744073709551615 1; t) := by
  rfl

-- register_alu_OR_1_1
example (s : riscv_state) : «dfn'OR» (1,1,2) (fixture s 18446744073709551615 1) =
 (let t := fixture s 18446744073709551615 1; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((18446744073709551615 : BitVec 64) ||| (1 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
  have symbolic := (show «dfn'OR» (1,1,2) (fixture s 18446744073709551615 1) = (let t := fixture s 18446744073709551615 1; {t with c_gpr := holUpdate 7 (holUpdate 1 ((18446744073709551615 : BitVec 64) ||| (1 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_OR_1_2
example (s : riscv_state) : «dfn'OR» (2,1,2) (fixture s 18446744073709551615 1) =
 (let t := fixture s 18446744073709551615 1; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((18446744073709551615 : BitVec 64) ||| (1 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
  have symbolic := (show «dfn'OR» (2,1,2) (fixture s 18446744073709551615 1) = (let t := fixture s 18446744073709551615 1; {t with c_gpr := holUpdate 7 (holUpdate 2 ((18446744073709551615 : BitVec 64) ||| (1 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_OR_1_7
example (s : riscv_state) : «dfn'OR» (7,1,2) (fixture s 18446744073709551615 1) =
 (let t := fixture s 18446744073709551615 1; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((18446744073709551615 : BitVec 64) ||| (1 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
  have symbolic := (show «dfn'OR» (7,1,2) (fixture s 18446744073709551615 1) = (let t := fixture s 18446744073709551615 1; {t with c_gpr := holUpdate 7 (holUpdate 7 ((18446744073709551615 : BitVec 64) ||| (1 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_OR_2_0
example (s : riscv_state) : «dfn'OR» (0,1,2) (fixture s 0 1) =
 (let t := fixture s 0 1; t) := by
  rfl

-- register_alu_OR_2_1
example (s : riscv_state) : «dfn'OR» (1,1,2) (fixture s 0 1) =
 (let t := fixture s 0 1; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) ||| (1 : BitVec 64)) = (1 : BitVec 64) := by decide
  have symbolic := (show «dfn'OR» (1,1,2) (fixture s 0 1) = (let t := fixture s 0 1; {t with c_gpr := holUpdate 7 (holUpdate 1 ((0 : BitVec 64) ||| (1 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_OR_2_2
example (s : riscv_state) : «dfn'OR» (2,1,2) (fixture s 0 1) =
 (let t := fixture s 0 1; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) ||| (1 : BitVec 64)) = (1 : BitVec 64) := by decide
  have symbolic := (show «dfn'OR» (2,1,2) (fixture s 0 1) = (let t := fixture s 0 1; {t with c_gpr := holUpdate 7 (holUpdate 2 ((0 : BitVec 64) ||| (1 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_OR_2_7
example (s : riscv_state) : «dfn'OR» (7,1,2) (fixture s 0 1) =
 (let t := fixture s 0 1; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) ||| (1 : BitVec 64)) = (1 : BitVec 64) := by decide
  have symbolic := (show «dfn'OR» (7,1,2) (fixture s 0 1) = (let t := fixture s 0 1; {t with c_gpr := holUpdate 7 (holUpdate 7 ((0 : BitVec 64) ||| (1 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_OR_3_0
example (s : riscv_state) : «dfn'OR» (0,1,2) (fixture s 9223372036854775808 18446744073709551615) =
 (let t := fixture s 9223372036854775808 18446744073709551615; t) := by
  rfl

-- register_alu_OR_3_1
example (s : riscv_state) : «dfn'OR» (1,1,2) (fixture s 9223372036854775808 18446744073709551615) =
 (let t := fixture s 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((9223372036854775808 : BitVec 64) ||| (18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
  have symbolic := (show «dfn'OR» (1,1,2) (fixture s 9223372036854775808 18446744073709551615) = (let t := fixture s 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 ((9223372036854775808 : BitVec 64) ||| (18446744073709551615 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_OR_3_2
example (s : riscv_state) : «dfn'OR» (2,1,2) (fixture s 9223372036854775808 18446744073709551615) =
 (let t := fixture s 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((9223372036854775808 : BitVec 64) ||| (18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
  have symbolic := (show «dfn'OR» (2,1,2) (fixture s 9223372036854775808 18446744073709551615) = (let t := fixture s 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 ((9223372036854775808 : BitVec 64) ||| (18446744073709551615 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_OR_3_7
example (s : riscv_state) : «dfn'OR» (7,1,2) (fixture s 9223372036854775808 18446744073709551615) =
 (let t := fixture s 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((9223372036854775808 : BitVec 64) ||| (18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
  have symbolic := (show «dfn'OR» (7,1,2) (fixture s 9223372036854775808 18446744073709551615) = (let t := fixture s 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 ((9223372036854775808 : BitVec 64) ||| (18446744073709551615 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_OR_4_0
example (s : riscv_state) : «dfn'OR» (0,1,2) (fixture s 12297829382473034410 6148914691236517205) =
 (let t := fixture s 12297829382473034410 6148914691236517205; t) := by
  rfl

-- register_alu_OR_4_1
example (s : riscv_state) : «dfn'OR» (1,1,2) (fixture s 12297829382473034410 6148914691236517205) =
 (let t := fixture s 12297829382473034410 6148914691236517205; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((12297829382473034410 : BitVec 64) ||| (6148914691236517205 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
  have symbolic := (show «dfn'OR» (1,1,2) (fixture s 12297829382473034410 6148914691236517205) = (let t := fixture s 12297829382473034410 6148914691236517205; {t with c_gpr := holUpdate 7 (holUpdate 1 ((12297829382473034410 : BitVec 64) ||| (6148914691236517205 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_OR_4_2
example (s : riscv_state) : «dfn'OR» (2,1,2) (fixture s 12297829382473034410 6148914691236517205) =
 (let t := fixture s 12297829382473034410 6148914691236517205; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((12297829382473034410 : BitVec 64) ||| (6148914691236517205 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
  have symbolic := (show «dfn'OR» (2,1,2) (fixture s 12297829382473034410 6148914691236517205) = (let t := fixture s 12297829382473034410 6148914691236517205; {t with c_gpr := holUpdate 7 (holUpdate 2 ((12297829382473034410 : BitVec 64) ||| (6148914691236517205 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_OR_4_7
example (s : riscv_state) : «dfn'OR» (7,1,2) (fixture s 12297829382473034410 6148914691236517205) =
 (let t := fixture s 12297829382473034410 6148914691236517205; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((12297829382473034410 : BitVec 64) ||| (6148914691236517205 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
  have symbolic := (show «dfn'OR» (7,1,2) (fixture s 12297829382473034410 6148914691236517205) = (let t := fixture s 12297829382473034410 6148914691236517205; {t with c_gpr := holUpdate 7 (holUpdate 7 ((12297829382473034410 : BitVec 64) ||| (6148914691236517205 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_OR_5_0
example (s : riscv_state) : «dfn'OR» (0,1,2) (fixture s 4294967297 1) =
 (let t := fixture s 4294967297 1; t) := by
  rfl

-- register_alu_OR_5_1
example (s : riscv_state) : «dfn'OR» (1,1,2) (fixture s 4294967297 1) =
 (let t := fixture s 4294967297 1; {t with c_gpr := holUpdate 7 (holUpdate 1 4294967297 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((4294967297 : BitVec 64) ||| (1 : BitVec 64)) = (4294967297 : BitVec 64) := by decide
  have symbolic := (show «dfn'OR» (1,1,2) (fixture s 4294967297 1) = (let t := fixture s 4294967297 1; {t with c_gpr := holUpdate 7 (holUpdate 1 ((4294967297 : BitVec 64) ||| (1 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_OR_5_2
example (s : riscv_state) : «dfn'OR» (2,1,2) (fixture s 4294967297 1) =
 (let t := fixture s 4294967297 1; {t with c_gpr := holUpdate 7 (holUpdate 2 4294967297 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((4294967297 : BitVec 64) ||| (1 : BitVec 64)) = (4294967297 : BitVec 64) := by decide
  have symbolic := (show «dfn'OR» (2,1,2) (fixture s 4294967297 1) = (let t := fixture s 4294967297 1; {t with c_gpr := holUpdate 7 (holUpdate 2 ((4294967297 : BitVec 64) ||| (1 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_OR_5_7
example (s : riscv_state) : «dfn'OR» (7,1,2) (fixture s 4294967297 1) =
 (let t := fixture s 4294967297 1; {t with c_gpr := holUpdate 7 (holUpdate 7 4294967297 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((4294967297 : BitVec 64) ||| (1 : BitVec 64)) = (4294967297 : BitVec 64) := by decide
  have symbolic := (show «dfn'OR» (7,1,2) (fixture s 4294967297 1) = (let t := fixture s 4294967297 1; {t with c_gpr := holUpdate 7 (holUpdate 7 ((4294967297 : BitVec 64) ||| (1 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_OR_6_0
example (s : riscv_state) : «dfn'OR» (0,0,2) (fixture s 18446744073709551615 17) =
 (let t := fixture s 18446744073709551615 17; t) := by
  rfl

-- register_alu_OR_6_1
example (s : riscv_state) : «dfn'OR» (1,0,2) (fixture s 18446744073709551615 17) =
 (let t := fixture s 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 1 17 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) ||| (17 : BitVec 64)) = (17 : BitVec 64) := by decide
  have symbolic := (show «dfn'OR» (1,0,2) (fixture s 18446744073709551615 17) = (let t := fixture s 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 1 ((0 : BitVec 64) ||| (17 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_OR_6_2
example (s : riscv_state) : «dfn'OR» (2,0,2) (fixture s 18446744073709551615 17) =
 (let t := fixture s 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 2 17 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) ||| (17 : BitVec 64)) = (17 : BitVec 64) := by decide
  have symbolic := (show «dfn'OR» (2,0,2) (fixture s 18446744073709551615 17) = (let t := fixture s 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 2 ((0 : BitVec 64) ||| (17 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_OR_6_7
example (s : riscv_state) : «dfn'OR» (7,0,2) (fixture s 18446744073709551615 17) =
 (let t := fixture s 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 7 17 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) ||| (17 : BitVec 64)) = (17 : BitVec 64) := by decide
  have symbolic := (show «dfn'OR» (7,0,2) (fixture s 18446744073709551615 17) = (let t := fixture s 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 7 ((0 : BitVec 64) ||| (17 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_OR_7_0
example (s : riscv_state) : «dfn'OR» (0,1,0) (fixture s 17 18446744073709551615) =
 (let t := fixture s 17 18446744073709551615; t) := by
  rfl

-- register_alu_OR_7_1
example (s : riscv_state) : «dfn'OR» (1,1,0) (fixture s 17 18446744073709551615) =
 (let t := fixture s 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 17 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((17 : BitVec 64) ||| (0 : BitVec 64)) = (17 : BitVec 64) := by decide
  have symbolic := (show «dfn'OR» (1,1,0) (fixture s 17 18446744073709551615) = (let t := fixture s 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 ((17 : BitVec 64) ||| (0 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_OR_7_2
example (s : riscv_state) : «dfn'OR» (2,1,0) (fixture s 17 18446744073709551615) =
 (let t := fixture s 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 17 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((17 : BitVec 64) ||| (0 : BitVec 64)) = (17 : BitVec 64) := by decide
  have symbolic := (show «dfn'OR» (2,1,0) (fixture s 17 18446744073709551615) = (let t := fixture s 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 ((17 : BitVec 64) ||| (0 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_OR_7_7
example (s : riscv_state) : «dfn'OR» (7,1,0) (fixture s 17 18446744073709551615) =
 (let t := fixture s 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 17 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((17 : BitVec 64) ||| (0 : BitVec 64)) = (17 : BitVec 64) := by decide
  have symbolic := (show «dfn'OR» (7,1,0) (fixture s 17 18446744073709551615) = (let t := fixture s 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 ((17 : BitVec 64) ||| (0 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_XOR_0_0
example (s : riscv_state) : «dfn'XOR» (0,1,2) (fixture s 0 0) =
 (let t := fixture s 0 0; t) := by
  rfl

-- register_alu_XOR_0_1
example (s : riscv_state) : «dfn'XOR» (1,1,2) (fixture s 0 0) =
 (let t := fixture s 0 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) ^^^ (0 : BitVec 64)) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'XOR» (1,1,2) (fixture s 0 0) = (let t := fixture s 0 0; {t with c_gpr := holUpdate 7 (holUpdate 1 ((0 : BitVec 64) ^^^ (0 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_XOR_0_2
example (s : riscv_state) : «dfn'XOR» (2,1,2) (fixture s 0 0) =
 (let t := fixture s 0 0; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) ^^^ (0 : BitVec 64)) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'XOR» (2,1,2) (fixture s 0 0) = (let t := fixture s 0 0; {t with c_gpr := holUpdate 7 (holUpdate 2 ((0 : BitVec 64) ^^^ (0 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_XOR_0_7
example (s : riscv_state) : «dfn'XOR» (7,1,2) (fixture s 0 0) =
 (let t := fixture s 0 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) ^^^ (0 : BitVec 64)) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'XOR» (7,1,2) (fixture s 0 0) = (let t := fixture s 0 0; {t with c_gpr := holUpdate 7 (holUpdate 7 ((0 : BitVec 64) ^^^ (0 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_XOR_1_0
example (s : riscv_state) : «dfn'XOR» (0,1,2) (fixture s 18446744073709551615 1) =
 (let t := fixture s 18446744073709551615 1; t) := by
  rfl

-- register_alu_XOR_1_1
example (s : riscv_state) : «dfn'XOR» (1,1,2) (fixture s 18446744073709551615 1) =
 (let t := fixture s 18446744073709551615 1; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((18446744073709551615 : BitVec 64) ^^^ (1 : BitVec 64)) = (18446744073709551614 : BitVec 64) := by decide
  have symbolic := (show «dfn'XOR» (1,1,2) (fixture s 18446744073709551615 1) = (let t := fixture s 18446744073709551615 1; {t with c_gpr := holUpdate 7 (holUpdate 1 ((18446744073709551615 : BitVec 64) ^^^ (1 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_XOR_1_2
example (s : riscv_state) : «dfn'XOR» (2,1,2) (fixture s 18446744073709551615 1) =
 (let t := fixture s 18446744073709551615 1; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((18446744073709551615 : BitVec 64) ^^^ (1 : BitVec 64)) = (18446744073709551614 : BitVec 64) := by decide
  have symbolic := (show «dfn'XOR» (2,1,2) (fixture s 18446744073709551615 1) = (let t := fixture s 18446744073709551615 1; {t with c_gpr := holUpdate 7 (holUpdate 2 ((18446744073709551615 : BitVec 64) ^^^ (1 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_XOR_1_7
example (s : riscv_state) : «dfn'XOR» (7,1,2) (fixture s 18446744073709551615 1) =
 (let t := fixture s 18446744073709551615 1; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((18446744073709551615 : BitVec 64) ^^^ (1 : BitVec 64)) = (18446744073709551614 : BitVec 64) := by decide
  have symbolic := (show «dfn'XOR» (7,1,2) (fixture s 18446744073709551615 1) = (let t := fixture s 18446744073709551615 1; {t with c_gpr := holUpdate 7 (holUpdate 7 ((18446744073709551615 : BitVec 64) ^^^ (1 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_XOR_2_0
example (s : riscv_state) : «dfn'XOR» (0,1,2) (fixture s 0 1) =
 (let t := fixture s 0 1; t) := by
  rfl

-- register_alu_XOR_2_1
example (s : riscv_state) : «dfn'XOR» (1,1,2) (fixture s 0 1) =
 (let t := fixture s 0 1; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) ^^^ (1 : BitVec 64)) = (1 : BitVec 64) := by decide
  have symbolic := (show «dfn'XOR» (1,1,2) (fixture s 0 1) = (let t := fixture s 0 1; {t with c_gpr := holUpdate 7 (holUpdate 1 ((0 : BitVec 64) ^^^ (1 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_XOR_2_2
example (s : riscv_state) : «dfn'XOR» (2,1,2) (fixture s 0 1) =
 (let t := fixture s 0 1; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) ^^^ (1 : BitVec 64)) = (1 : BitVec 64) := by decide
  have symbolic := (show «dfn'XOR» (2,1,2) (fixture s 0 1) = (let t := fixture s 0 1; {t with c_gpr := holUpdate 7 (holUpdate 2 ((0 : BitVec 64) ^^^ (1 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_XOR_2_7
example (s : riscv_state) : «dfn'XOR» (7,1,2) (fixture s 0 1) =
 (let t := fixture s 0 1; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) ^^^ (1 : BitVec 64)) = (1 : BitVec 64) := by decide
  have symbolic := (show «dfn'XOR» (7,1,2) (fixture s 0 1) = (let t := fixture s 0 1; {t with c_gpr := holUpdate 7 (holUpdate 7 ((0 : BitVec 64) ^^^ (1 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_XOR_3_0
example (s : riscv_state) : «dfn'XOR» (0,1,2) (fixture s 9223372036854775808 18446744073709551615) =
 (let t := fixture s 9223372036854775808 18446744073709551615; t) := by
  rfl

-- register_alu_XOR_3_1
example (s : riscv_state) : «dfn'XOR» (1,1,2) (fixture s 9223372036854775808 18446744073709551615) =
 (let t := fixture s 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 9223372036854775807 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((9223372036854775808 : BitVec 64) ^^^ (18446744073709551615 : BitVec 64)) = (9223372036854775807 : BitVec 64) := by decide
  have symbolic := (show «dfn'XOR» (1,1,2) (fixture s 9223372036854775808 18446744073709551615) = (let t := fixture s 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 ((9223372036854775808 : BitVec 64) ^^^ (18446744073709551615 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_XOR_3_2
example (s : riscv_state) : «dfn'XOR» (2,1,2) (fixture s 9223372036854775808 18446744073709551615) =
 (let t := fixture s 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 9223372036854775807 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((9223372036854775808 : BitVec 64) ^^^ (18446744073709551615 : BitVec 64)) = (9223372036854775807 : BitVec 64) := by decide
  have symbolic := (show «dfn'XOR» (2,1,2) (fixture s 9223372036854775808 18446744073709551615) = (let t := fixture s 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 ((9223372036854775808 : BitVec 64) ^^^ (18446744073709551615 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_XOR_3_7
example (s : riscv_state) : «dfn'XOR» (7,1,2) (fixture s 9223372036854775808 18446744073709551615) =
 (let t := fixture s 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 9223372036854775807 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((9223372036854775808 : BitVec 64) ^^^ (18446744073709551615 : BitVec 64)) = (9223372036854775807 : BitVec 64) := by decide
  have symbolic := (show «dfn'XOR» (7,1,2) (fixture s 9223372036854775808 18446744073709551615) = (let t := fixture s 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 ((9223372036854775808 : BitVec 64) ^^^ (18446744073709551615 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_XOR_4_0
example (s : riscv_state) : «dfn'XOR» (0,1,2) (fixture s 12297829382473034410 6148914691236517205) =
 (let t := fixture s 12297829382473034410 6148914691236517205; t) := by
  rfl

-- register_alu_XOR_4_1
example (s : riscv_state) : «dfn'XOR» (1,1,2) (fixture s 12297829382473034410 6148914691236517205) =
 (let t := fixture s 12297829382473034410 6148914691236517205; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((12297829382473034410 : BitVec 64) ^^^ (6148914691236517205 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
  have symbolic := (show «dfn'XOR» (1,1,2) (fixture s 12297829382473034410 6148914691236517205) = (let t := fixture s 12297829382473034410 6148914691236517205; {t with c_gpr := holUpdate 7 (holUpdate 1 ((12297829382473034410 : BitVec 64) ^^^ (6148914691236517205 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_XOR_4_2
example (s : riscv_state) : «dfn'XOR» (2,1,2) (fixture s 12297829382473034410 6148914691236517205) =
 (let t := fixture s 12297829382473034410 6148914691236517205; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((12297829382473034410 : BitVec 64) ^^^ (6148914691236517205 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
  have symbolic := (show «dfn'XOR» (2,1,2) (fixture s 12297829382473034410 6148914691236517205) = (let t := fixture s 12297829382473034410 6148914691236517205; {t with c_gpr := holUpdate 7 (holUpdate 2 ((12297829382473034410 : BitVec 64) ^^^ (6148914691236517205 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_XOR_4_7
example (s : riscv_state) : «dfn'XOR» (7,1,2) (fixture s 12297829382473034410 6148914691236517205) =
 (let t := fixture s 12297829382473034410 6148914691236517205; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((12297829382473034410 : BitVec 64) ^^^ (6148914691236517205 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
  have symbolic := (show «dfn'XOR» (7,1,2) (fixture s 12297829382473034410 6148914691236517205) = (let t := fixture s 12297829382473034410 6148914691236517205; {t with c_gpr := holUpdate 7 (holUpdate 7 ((12297829382473034410 : BitVec 64) ^^^ (6148914691236517205 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_XOR_5_0
example (s : riscv_state) : «dfn'XOR» (0,1,2) (fixture s 4294967297 1) =
 (let t := fixture s 4294967297 1; t) := by
  rfl

-- register_alu_XOR_5_1
example (s : riscv_state) : «dfn'XOR» (1,1,2) (fixture s 4294967297 1) =
 (let t := fixture s 4294967297 1; {t with c_gpr := holUpdate 7 (holUpdate 1 4294967296 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((4294967297 : BitVec 64) ^^^ (1 : BitVec 64)) = (4294967296 : BitVec 64) := by decide
  have symbolic := (show «dfn'XOR» (1,1,2) (fixture s 4294967297 1) = (let t := fixture s 4294967297 1; {t with c_gpr := holUpdate 7 (holUpdate 1 ((4294967297 : BitVec 64) ^^^ (1 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_XOR_5_2
example (s : riscv_state) : «dfn'XOR» (2,1,2) (fixture s 4294967297 1) =
 (let t := fixture s 4294967297 1; {t with c_gpr := holUpdate 7 (holUpdate 2 4294967296 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((4294967297 : BitVec 64) ^^^ (1 : BitVec 64)) = (4294967296 : BitVec 64) := by decide
  have symbolic := (show «dfn'XOR» (2,1,2) (fixture s 4294967297 1) = (let t := fixture s 4294967297 1; {t with c_gpr := holUpdate 7 (holUpdate 2 ((4294967297 : BitVec 64) ^^^ (1 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_XOR_5_7
example (s : riscv_state) : «dfn'XOR» (7,1,2) (fixture s 4294967297 1) =
 (let t := fixture s 4294967297 1; {t with c_gpr := holUpdate 7 (holUpdate 7 4294967296 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((4294967297 : BitVec 64) ^^^ (1 : BitVec 64)) = (4294967296 : BitVec 64) := by decide
  have symbolic := (show «dfn'XOR» (7,1,2) (fixture s 4294967297 1) = (let t := fixture s 4294967297 1; {t with c_gpr := holUpdate 7 (holUpdate 7 ((4294967297 : BitVec 64) ^^^ (1 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_XOR_6_0
example (s : riscv_state) : «dfn'XOR» (0,0,2) (fixture s 18446744073709551615 17) =
 (let t := fixture s 18446744073709551615 17; t) := by
  rfl

-- register_alu_XOR_6_1
example (s : riscv_state) : «dfn'XOR» (1,0,2) (fixture s 18446744073709551615 17) =
 (let t := fixture s 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 1 17 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) ^^^ (17 : BitVec 64)) = (17 : BitVec 64) := by decide
  have symbolic := (show «dfn'XOR» (1,0,2) (fixture s 18446744073709551615 17) = (let t := fixture s 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 1 ((0 : BitVec 64) ^^^ (17 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_XOR_6_2
example (s : riscv_state) : «dfn'XOR» (2,0,2) (fixture s 18446744073709551615 17) =
 (let t := fixture s 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 2 17 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) ^^^ (17 : BitVec 64)) = (17 : BitVec 64) := by decide
  have symbolic := (show «dfn'XOR» (2,0,2) (fixture s 18446744073709551615 17) = (let t := fixture s 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 2 ((0 : BitVec 64) ^^^ (17 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_XOR_6_7
example (s : riscv_state) : «dfn'XOR» (7,0,2) (fixture s 18446744073709551615 17) =
 (let t := fixture s 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 7 17 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((0 : BitVec 64) ^^^ (17 : BitVec 64)) = (17 : BitVec 64) := by decide
  have symbolic := (show «dfn'XOR» (7,0,2) (fixture s 18446744073709551615 17) = (let t := fixture s 18446744073709551615 17; {t with c_gpr := holUpdate 7 (holUpdate 7 ((0 : BitVec 64) ^^^ (17 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_XOR_7_0
example (s : riscv_state) : «dfn'XOR» (0,1,0) (fixture s 17 18446744073709551615) =
 (let t := fixture s 17 18446744073709551615; t) := by
  rfl

-- register_alu_XOR_7_1
example (s : riscv_state) : «dfn'XOR» (1,1,0) (fixture s 17 18446744073709551615) =
 (let t := fixture s 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 17 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((17 : BitVec 64) ^^^ (0 : BitVec 64)) = (17 : BitVec 64) := by decide
  have symbolic := (show «dfn'XOR» (1,1,0) (fixture s 17 18446744073709551615) = (let t := fixture s 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 ((17 : BitVec 64) ^^^ (0 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_XOR_7_2
example (s : riscv_state) : «dfn'XOR» (2,1,0) (fixture s 17 18446744073709551615) =
 (let t := fixture s 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 17 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((17 : BitVec 64) ^^^ (0 : BitVec 64)) = (17 : BitVec 64) := by decide
  have symbolic := (show «dfn'XOR» (2,1,0) (fixture s 17 18446744073709551615) = (let t := fixture s 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 ((17 : BitVec 64) ^^^ (0 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

-- register_alu_XOR_7_7
example (s : riscv_state) : «dfn'XOR» (7,1,0) (fixture s 17 18446744073709551615) =
 (let t := fixture s 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 17 (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((17 : BitVec 64) ^^^ (0 : BitVec 64)) = (17 : BitVec 64) := by decide
  have symbolic := (show «dfn'XOR» (7,1,0) (fixture s 17 18446744073709551615) = (let t := fixture s 17 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 ((17 : BitVec 64) ^^^ (0 : BitVec 64)) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

end Flapjack.Test.L3RegisterALUParity
