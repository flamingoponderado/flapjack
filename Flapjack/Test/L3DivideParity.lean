import Flapjack.RiscV.L3.Defs.Divide
set_option maxRecDepth 20000
namespace Flapjack.Test.L3DivideParity
open Flapjack.RiscV.L3
private def fixture (s : riscv_state) (mode : BitVec 2) (a b : BitVec 64) : riscv_state :=
 {s with procID := 7, c_MCSR := fun id => {s.c_MCSR id with mcpuid := {(s.c_MCSR id).mcpuid with ArchBase := mode}}, c_gpr := fun id r => if r = 1 then a else if r = 2 then b else s.c_gpr id r}

/-- Test infrastructure: destination zero suppresses the numeric write. -/
private theorem zeroWrite (w : BitVec 64) (s : riscv_state) : «write'GPR» (w,0) s = s := by rfl

-- divide_DIV_0_0_0
example (s : riscv_state) : «dfn'DIV» (0,1,2) (fixture s 0 0 0) = (let t := fixture s 0 0 0; t) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 0 0 0) else «write'GPR» (BitVec.sdiv (0 : BitVec 64) (0 : BitVec 64), 0) (fixture s 0 0 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 0 0 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_0_1
example (s : riscv_state) : «dfn'DIV» (1,1,2) (fixture s 0 0 0) = (let t := fixture s 0 0 0; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 0 0 0) else «write'GPR» (BitVec.sdiv (0 : BitVec 64) (0 : BitVec 64), 1) (fixture s 0 0 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 0 0 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_0_2
example (s : riscv_state) : «dfn'DIV» (2,1,2) (fixture s 0 0 0) = (let t := fixture s 0 0 0; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 0 0 0) else «write'GPR» (BitVec.sdiv (0 : BitVec 64) (0 : BitVec 64), 2) (fixture s 0 0 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 0 0 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_0_7
example (s : riscv_state) : «dfn'DIV» (7,1,2) (fixture s 0 0 0) = (let t := fixture s 0 0 0; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 0 0 0) else «write'GPR» (BitVec.sdiv (0 : BitVec 64) (0 : BitVec 64), 7) (fixture s 0 0 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 0 0 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_1_0
example (s : riscv_state) : «dfn'DIV» (0,1,2) (fixture s 0 17 0) = (let t := fixture s 0 17 0; t) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 0 17 0) else «write'GPR» (BitVec.sdiv (17 : BitVec 64) (0 : BitVec 64), 0) (fixture s 0 17 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 0 17 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_1_1
example (s : riscv_state) : «dfn'DIV» (1,1,2) (fixture s 0 17 0) = (let t := fixture s 0 17 0; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 0 17 0) else «write'GPR» (BitVec.sdiv (17 : BitVec 64) (0 : BitVec 64), 1) (fixture s 0 17 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 0 17 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_1_2
example (s : riscv_state) : «dfn'DIV» (2,1,2) (fixture s 0 17 0) = (let t := fixture s 0 17 0; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 0 17 0) else «write'GPR» (BitVec.sdiv (17 : BitVec 64) (0 : BitVec 64), 2) (fixture s 0 17 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 0 17 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_1_7
example (s : riscv_state) : «dfn'DIV» (7,1,2) (fixture s 0 17 0) = (let t := fixture s 0 17 0; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 0 17 0) else «write'GPR» (BitVec.sdiv (17 : BitVec 64) (0 : BitVec 64), 7) (fixture s 0 17 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 0 17 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_2_0
example (s : riscv_state) : «dfn'DIV» (0,1,2) (fixture s 0 18446744073709551615 0) = (let t := fixture s 0 18446744073709551615 0; t) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 0 18446744073709551615 0) else «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (0 : BitVec 64), 0) (fixture s 0 18446744073709551615 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 0 18446744073709551615 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_2_1
example (s : riscv_state) : «dfn'DIV» (1,1,2) (fixture s 0 18446744073709551615 0) = (let t := fixture s 0 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 0 18446744073709551615 0) else «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (0 : BitVec 64), 1) (fixture s 0 18446744073709551615 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 0 18446744073709551615 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_2_2
example (s : riscv_state) : «dfn'DIV» (2,1,2) (fixture s 0 18446744073709551615 0) = (let t := fixture s 0 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 0 18446744073709551615 0) else «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (0 : BitVec 64), 2) (fixture s 0 18446744073709551615 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 0 18446744073709551615 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_2_7
example (s : riscv_state) : «dfn'DIV» (7,1,2) (fixture s 0 18446744073709551615 0) = (let t := fixture s 0 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 0 18446744073709551615 0) else «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (0 : BitVec 64), 7) (fixture s 0 18446744073709551615 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 0 18446744073709551615 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_3_0
example (s : riscv_state) : «dfn'DIV» (0,1,2) (fixture s 0 17 3) = (let t := fixture s 0 17 3; t) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 0 17 3) else «write'GPR» (BitVec.sdiv (17 : BitVec 64) (3 : BitVec 64), 0) (fixture s 0 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (17 : BitVec 64) (3 : BitVec 64), 0) (fixture s 0 17 3) = _
 have numeric : (BitVec.sdiv (17 : BitVec 64) (3 : BitVec 64)) = (5 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_3_1
example (s : riscv_state) : «dfn'DIV» (1,1,2) (fixture s 0 17 3) = (let t := fixture s 0 17 3; {t with c_gpr := holUpdate 7 (holUpdate 1 5 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 0 17 3) else «write'GPR» (BitVec.sdiv (17 : BitVec 64) (3 : BitVec 64), 1) (fixture s 0 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (17 : BitVec 64) (3 : BitVec 64), 1) (fixture s 0 17 3) = _
 have numeric : (BitVec.sdiv (17 : BitVec 64) (3 : BitVec 64)) = (5 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_3_2
example (s : riscv_state) : «dfn'DIV» (2,1,2) (fixture s 0 17 3) = (let t := fixture s 0 17 3; {t with c_gpr := holUpdate 7 (holUpdate 2 5 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 0 17 3) else «write'GPR» (BitVec.sdiv (17 : BitVec 64) (3 : BitVec 64), 2) (fixture s 0 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (17 : BitVec 64) (3 : BitVec 64), 2) (fixture s 0 17 3) = _
 have numeric : (BitVec.sdiv (17 : BitVec 64) (3 : BitVec 64)) = (5 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_3_7
example (s : riscv_state) : «dfn'DIV» (7,1,2) (fixture s 0 17 3) = (let t := fixture s 0 17 3; {t with c_gpr := holUpdate 7 (holUpdate 7 5 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 0 17 3) else «write'GPR» (BitVec.sdiv (17 : BitVec 64) (3 : BitVec 64), 7) (fixture s 0 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (17 : BitVec 64) (3 : BitVec 64), 7) (fixture s 0 17 3) = _
 have numeric : (BitVec.sdiv (17 : BitVec 64) (3 : BitVec 64)) = (5 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_4_0
example (s : riscv_state) : «dfn'DIV» (0,1,2) (fixture s 0 18446744073709551599 3) = (let t := fixture s 0 18446744073709551599 3; t) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 0 18446744073709551599 3) else «write'GPR» (BitVec.sdiv (18446744073709551599 : BitVec 64) (3 : BitVec 64), 0) (fixture s 0 18446744073709551599 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (18446744073709551599 : BitVec 64) (3 : BitVec 64), 0) (fixture s 0 18446744073709551599 3) = _
 have numeric : (BitVec.sdiv (18446744073709551599 : BitVec 64) (3 : BitVec 64)) = (18446744073709551611 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_4_1
example (s : riscv_state) : «dfn'DIV» (1,1,2) (fixture s 0 18446744073709551599 3) = (let t := fixture s 0 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551611 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 0 18446744073709551599 3) else «write'GPR» (BitVec.sdiv (18446744073709551599 : BitVec 64) (3 : BitVec 64), 1) (fixture s 0 18446744073709551599 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (18446744073709551599 : BitVec 64) (3 : BitVec 64), 1) (fixture s 0 18446744073709551599 3) = _
 have numeric : (BitVec.sdiv (18446744073709551599 : BitVec 64) (3 : BitVec 64)) = (18446744073709551611 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_4_2
example (s : riscv_state) : «dfn'DIV» (2,1,2) (fixture s 0 18446744073709551599 3) = (let t := fixture s 0 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551611 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 0 18446744073709551599 3) else «write'GPR» (BitVec.sdiv (18446744073709551599 : BitVec 64) (3 : BitVec 64), 2) (fixture s 0 18446744073709551599 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (18446744073709551599 : BitVec 64) (3 : BitVec 64), 2) (fixture s 0 18446744073709551599 3) = _
 have numeric : (BitVec.sdiv (18446744073709551599 : BitVec 64) (3 : BitVec 64)) = (18446744073709551611 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_4_7
example (s : riscv_state) : «dfn'DIV» (7,1,2) (fixture s 0 18446744073709551599 3) = (let t := fixture s 0 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551611 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 0 18446744073709551599 3) else «write'GPR» (BitVec.sdiv (18446744073709551599 : BitVec 64) (3 : BitVec 64), 7) (fixture s 0 18446744073709551599 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (18446744073709551599 : BitVec 64) (3 : BitVec 64), 7) (fixture s 0 18446744073709551599 3) = _
 have numeric : (BitVec.sdiv (18446744073709551599 : BitVec 64) (3 : BitVec 64)) = (18446744073709551611 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_5_0
example (s : riscv_state) : «dfn'DIV» (0,1,2) (fixture s 0 17 18446744073709551613) = (let t := fixture s 0 17 18446744073709551613; t) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 0 17 18446744073709551613) else «write'GPR» (BitVec.sdiv (17 : BitVec 64) (18446744073709551613 : BitVec 64), 0) (fixture s 0 17 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (17 : BitVec 64) (18446744073709551613 : BitVec 64), 0) (fixture s 0 17 18446744073709551613) = _
 have numeric : (BitVec.sdiv (17 : BitVec 64) (18446744073709551613 : BitVec 64)) = (18446744073709551611 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_5_1
example (s : riscv_state) : «dfn'DIV» (1,1,2) (fixture s 0 17 18446744073709551613) = (let t := fixture s 0 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551611 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 0 17 18446744073709551613) else «write'GPR» (BitVec.sdiv (17 : BitVec 64) (18446744073709551613 : BitVec 64), 1) (fixture s 0 17 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (17 : BitVec 64) (18446744073709551613 : BitVec 64), 1) (fixture s 0 17 18446744073709551613) = _
 have numeric : (BitVec.sdiv (17 : BitVec 64) (18446744073709551613 : BitVec 64)) = (18446744073709551611 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_5_2
example (s : riscv_state) : «dfn'DIV» (2,1,2) (fixture s 0 17 18446744073709551613) = (let t := fixture s 0 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551611 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 0 17 18446744073709551613) else «write'GPR» (BitVec.sdiv (17 : BitVec 64) (18446744073709551613 : BitVec 64), 2) (fixture s 0 17 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (17 : BitVec 64) (18446744073709551613 : BitVec 64), 2) (fixture s 0 17 18446744073709551613) = _
 have numeric : (BitVec.sdiv (17 : BitVec 64) (18446744073709551613 : BitVec 64)) = (18446744073709551611 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_5_7
example (s : riscv_state) : «dfn'DIV» (7,1,2) (fixture s 0 17 18446744073709551613) = (let t := fixture s 0 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551611 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 0 17 18446744073709551613) else «write'GPR» (BitVec.sdiv (17 : BitVec 64) (18446744073709551613 : BitVec 64), 7) (fixture s 0 17 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (17 : BitVec 64) (18446744073709551613 : BitVec 64), 7) (fixture s 0 17 18446744073709551613) = _
 have numeric : (BitVec.sdiv (17 : BitVec 64) (18446744073709551613 : BitVec 64)) = (18446744073709551611 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_6_0
example (s : riscv_state) : «dfn'DIV» (0,1,2) (fixture s 0 18446744073709551599 18446744073709551613) = (let t := fixture s 0 18446744073709551599 18446744073709551613; t) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 0 18446744073709551599 18446744073709551613) else «write'GPR» (BitVec.sdiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 0) (fixture s 0 18446744073709551599 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 0) (fixture s 0 18446744073709551599 18446744073709551613) = _
 have numeric : (BitVec.sdiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64)) = (5 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_6_1
example (s : riscv_state) : «dfn'DIV» (1,1,2) (fixture s 0 18446744073709551599 18446744073709551613) = (let t := fixture s 0 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 1 5 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 0 18446744073709551599 18446744073709551613) else «write'GPR» (BitVec.sdiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 1) (fixture s 0 18446744073709551599 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 1) (fixture s 0 18446744073709551599 18446744073709551613) = _
 have numeric : (BitVec.sdiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64)) = (5 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_6_2
example (s : riscv_state) : «dfn'DIV» (2,1,2) (fixture s 0 18446744073709551599 18446744073709551613) = (let t := fixture s 0 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 2 5 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 0 18446744073709551599 18446744073709551613) else «write'GPR» (BitVec.sdiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 2) (fixture s 0 18446744073709551599 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 2) (fixture s 0 18446744073709551599 18446744073709551613) = _
 have numeric : (BitVec.sdiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64)) = (5 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_6_7
example (s : riscv_state) : «dfn'DIV» (7,1,2) (fixture s 0 18446744073709551599 18446744073709551613) = (let t := fixture s 0 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 7 5 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 0 18446744073709551599 18446744073709551613) else «write'GPR» (BitVec.sdiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 7) (fixture s 0 18446744073709551599 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 7) (fixture s 0 18446744073709551599 18446744073709551613) = _
 have numeric : (BitVec.sdiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64)) = (5 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_7_0
example (s : riscv_state) : «dfn'DIV» (0,1,2) (fixture s 0 9223372036854775808 18446744073709551615) = (let t := fixture s 0 9223372036854775808 18446744073709551615; t) := by
 change (if ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 0 9223372036854775808 18446744073709551615) else «write'GPR» (BitVec.sdiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 0) (fixture s 0 9223372036854775808 18446744073709551615)) = _
 have divisorZero : ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 0) (fixture s 0 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.sdiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64)) = (9223372036854775808 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_7_1
example (s : riscv_state) : «dfn'DIV» (1,1,2) (fixture s 0 9223372036854775808 18446744073709551615) = (let t := fixture s 0 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 0 9223372036854775808 18446744073709551615) else «write'GPR» (BitVec.sdiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 1) (fixture s 0 9223372036854775808 18446744073709551615)) = _
 have divisorZero : ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 1) (fixture s 0 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.sdiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64)) = (9223372036854775808 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_7_2
example (s : riscv_state) : «dfn'DIV» (2,1,2) (fixture s 0 9223372036854775808 18446744073709551615) = (let t := fixture s 0 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 0 9223372036854775808 18446744073709551615) else «write'GPR» (BitVec.sdiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 2) (fixture s 0 9223372036854775808 18446744073709551615)) = _
 have divisorZero : ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 2) (fixture s 0 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.sdiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64)) = (9223372036854775808 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_7_7
example (s : riscv_state) : «dfn'DIV» (7,1,2) (fixture s 0 9223372036854775808 18446744073709551615) = (let t := fixture s 0 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 0 9223372036854775808 18446744073709551615) else «write'GPR» (BitVec.sdiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 7) (fixture s 0 9223372036854775808 18446744073709551615)) = _
 have divisorZero : ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 7) (fixture s 0 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.sdiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64)) = (9223372036854775808 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_8_0
example (s : riscv_state) : «dfn'DIV» (0,1,2) (fixture s 0 2147483648 4294967295) = (let t := fixture s 0 2147483648 4294967295; t) := by
 change (if ((4294967295 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 0 2147483648 4294967295) else «write'GPR» (BitVec.sdiv (2147483648 : BitVec 64) (4294967295 : BitVec 64), 0) (fixture s 0 2147483648 4294967295)) = _
 have divisorZero : ((4294967295 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (2147483648 : BitVec 64) (4294967295 : BitVec 64), 0) (fixture s 0 2147483648 4294967295) = _
 have numeric : (BitVec.sdiv (2147483648 : BitVec 64) (4294967295 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_8_1
example (s : riscv_state) : «dfn'DIV» (1,1,2) (fixture s 0 2147483648 4294967295) = (let t := fixture s 0 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967295 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 0 2147483648 4294967295) else «write'GPR» (BitVec.sdiv (2147483648 : BitVec 64) (4294967295 : BitVec 64), 1) (fixture s 0 2147483648 4294967295)) = _
 have divisorZero : ((4294967295 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (2147483648 : BitVec 64) (4294967295 : BitVec 64), 1) (fixture s 0 2147483648 4294967295) = _
 have numeric : (BitVec.sdiv (2147483648 : BitVec 64) (4294967295 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_8_2
example (s : riscv_state) : «dfn'DIV» (2,1,2) (fixture s 0 2147483648 4294967295) = (let t := fixture s 0 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967295 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 0 2147483648 4294967295) else «write'GPR» (BitVec.sdiv (2147483648 : BitVec 64) (4294967295 : BitVec 64), 2) (fixture s 0 2147483648 4294967295)) = _
 have divisorZero : ((4294967295 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (2147483648 : BitVec 64) (4294967295 : BitVec 64), 2) (fixture s 0 2147483648 4294967295) = _
 have numeric : (BitVec.sdiv (2147483648 : BitVec 64) (4294967295 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_8_7
example (s : riscv_state) : «dfn'DIV» (7,1,2) (fixture s 0 2147483648 4294967295) = (let t := fixture s 0 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967295 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 0 2147483648 4294967295) else «write'GPR» (BitVec.sdiv (2147483648 : BitVec 64) (4294967295 : BitVec 64), 7) (fixture s 0 2147483648 4294967295)) = _
 have divisorZero : ((4294967295 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (2147483648 : BitVec 64) (4294967295 : BitVec 64), 7) (fixture s 0 2147483648 4294967295) = _
 have numeric : (BitVec.sdiv (2147483648 : BitVec 64) (4294967295 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_9_0
example (s : riscv_state) : «dfn'DIV» (0,1,2) (fixture s 0 4294967313 4294967296) = (let t := fixture s 0 4294967313 4294967296; t) := by
 change (if ((4294967296 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 0 4294967313 4294967296) else «write'GPR» (BitVec.sdiv (4294967313 : BitVec 64) (4294967296 : BitVec 64), 0) (fixture s 0 4294967313 4294967296)) = _
 have divisorZero : ((4294967296 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (4294967313 : BitVec 64) (4294967296 : BitVec 64), 0) (fixture s 0 4294967313 4294967296) = _
 have numeric : (BitVec.sdiv (4294967313 : BitVec 64) (4294967296 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_9_1
example (s : riscv_state) : «dfn'DIV» (1,1,2) (fixture s 0 4294967313 4294967296) = (let t := fixture s 0 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967296 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 0 4294967313 4294967296) else «write'GPR» (BitVec.sdiv (4294967313 : BitVec 64) (4294967296 : BitVec 64), 1) (fixture s 0 4294967313 4294967296)) = _
 have divisorZero : ((4294967296 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (4294967313 : BitVec 64) (4294967296 : BitVec 64), 1) (fixture s 0 4294967313 4294967296) = _
 have numeric : (BitVec.sdiv (4294967313 : BitVec 64) (4294967296 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_9_2
example (s : riscv_state) : «dfn'DIV» (2,1,2) (fixture s 0 4294967313 4294967296) = (let t := fixture s 0 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967296 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 0 4294967313 4294967296) else «write'GPR» (BitVec.sdiv (4294967313 : BitVec 64) (4294967296 : BitVec 64), 2) (fixture s 0 4294967313 4294967296)) = _
 have divisorZero : ((4294967296 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (4294967313 : BitVec 64) (4294967296 : BitVec 64), 2) (fixture s 0 4294967313 4294967296) = _
 have numeric : (BitVec.sdiv (4294967313 : BitVec 64) (4294967296 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_9_7
example (s : riscv_state) : «dfn'DIV» (7,1,2) (fixture s 0 4294967313 4294967296) = (let t := fixture s 0 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967296 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 0 4294967313 4294967296) else «write'GPR» (BitVec.sdiv (4294967313 : BitVec 64) (4294967296 : BitVec 64), 7) (fixture s 0 4294967313 4294967296)) = _
 have divisorZero : ((4294967296 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (4294967313 : BitVec 64) (4294967296 : BitVec 64), 7) (fixture s 0 4294967313 4294967296) = _
 have numeric : (BitVec.sdiv (4294967313 : BitVec 64) (4294967296 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_10_0
example (s : riscv_state) : «dfn'DIV» (0,1,2) (fixture s 0 18446744073709551615 2) = (let t := fixture s 0 18446744073709551615 2; t) := by
 change (if ((2 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 0 18446744073709551615 2) else «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (2 : BitVec 64), 0) (fixture s 0 18446744073709551615 2)) = _
 have divisorZero : ((2 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (2 : BitVec 64), 0) (fixture s 0 18446744073709551615 2) = _
 have numeric : (BitVec.sdiv (18446744073709551615 : BitVec 64) (2 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_10_1
example (s : riscv_state) : «dfn'DIV» (1,1,2) (fixture s 0 18446744073709551615 2) = (let t := fixture s 0 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((2 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 0 18446744073709551615 2) else «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (2 : BitVec 64), 1) (fixture s 0 18446744073709551615 2)) = _
 have divisorZero : ((2 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (2 : BitVec 64), 1) (fixture s 0 18446744073709551615 2) = _
 have numeric : (BitVec.sdiv (18446744073709551615 : BitVec 64) (2 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_10_2
example (s : riscv_state) : «dfn'DIV» (2,1,2) (fixture s 0 18446744073709551615 2) = (let t := fixture s 0 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((2 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 0 18446744073709551615 2) else «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (2 : BitVec 64), 2) (fixture s 0 18446744073709551615 2)) = _
 have divisorZero : ((2 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (2 : BitVec 64), 2) (fixture s 0 18446744073709551615 2) = _
 have numeric : (BitVec.sdiv (18446744073709551615 : BitVec 64) (2 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_10_7
example (s : riscv_state) : «dfn'DIV» (7,1,2) (fixture s 0 18446744073709551615 2) = (let t := fixture s 0 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((2 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 0 18446744073709551615 2) else «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (2 : BitVec 64), 7) (fixture s 0 18446744073709551615 2)) = _
 have divisorZero : ((2 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (2 : BitVec 64), 7) (fixture s 0 18446744073709551615 2) = _
 have numeric : (BitVec.sdiv (18446744073709551615 : BitVec 64) (2 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_11_0
example (s : riscv_state) : «dfn'DIV» (0,1,2) (fixture s 0 18446744073709551615 3) = (let t := fixture s 0 18446744073709551615 3; t) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 0 18446744073709551615 3) else «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (3 : BitVec 64), 0) (fixture s 0 18446744073709551615 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (3 : BitVec 64), 0) (fixture s 0 18446744073709551615 3) = _
 have numeric : (BitVec.sdiv (18446744073709551615 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_11_1
example (s : riscv_state) : «dfn'DIV» (1,1,2) (fixture s 0 18446744073709551615 3) = (let t := fixture s 0 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 0 18446744073709551615 3) else «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (3 : BitVec 64), 1) (fixture s 0 18446744073709551615 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (3 : BitVec 64), 1) (fixture s 0 18446744073709551615 3) = _
 have numeric : (BitVec.sdiv (18446744073709551615 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_11_2
example (s : riscv_state) : «dfn'DIV» (2,1,2) (fixture s 0 18446744073709551615 3) = (let t := fixture s 0 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 0 18446744073709551615 3) else «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (3 : BitVec 64), 2) (fixture s 0 18446744073709551615 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (3 : BitVec 64), 2) (fixture s 0 18446744073709551615 3) = _
 have numeric : (BitVec.sdiv (18446744073709551615 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_11_7
example (s : riscv_state) : «dfn'DIV» (7,1,2) (fixture s 0 18446744073709551615 3) = (let t := fixture s 0 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 0 18446744073709551615 3) else «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (3 : BitVec 64), 7) (fixture s 0 18446744073709551615 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (3 : BitVec 64), 7) (fixture s 0 18446744073709551615 3) = _
 have numeric : (BitVec.sdiv (18446744073709551615 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_12_0
example (s : riscv_state) : «dfn'DIV» (0,0,2) (fixture s 0 17 3) = (let t := fixture s 0 17 3; t) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 0 17 3) else «write'GPR» (BitVec.sdiv (0 : BitVec 64) (3 : BitVec 64), 0) (fixture s 0 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (0 : BitVec 64) (3 : BitVec 64), 0) (fixture s 0 17 3) = _
 have numeric : (BitVec.sdiv (0 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_12_1
example (s : riscv_state) : «dfn'DIV» (1,0,2) (fixture s 0 17 3) = (let t := fixture s 0 17 3; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 0 17 3) else «write'GPR» (BitVec.sdiv (0 : BitVec 64) (3 : BitVec 64), 1) (fixture s 0 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (0 : BitVec 64) (3 : BitVec 64), 1) (fixture s 0 17 3) = _
 have numeric : (BitVec.sdiv (0 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_12_2
example (s : riscv_state) : «dfn'DIV» (2,0,2) (fixture s 0 17 3) = (let t := fixture s 0 17 3; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 0 17 3) else «write'GPR» (BitVec.sdiv (0 : BitVec 64) (3 : BitVec 64), 2) (fixture s 0 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (0 : BitVec 64) (3 : BitVec 64), 2) (fixture s 0 17 3) = _
 have numeric : (BitVec.sdiv (0 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_12_7
example (s : riscv_state) : «dfn'DIV» (7,0,2) (fixture s 0 17 3) = (let t := fixture s 0 17 3; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 0 17 3) else «write'GPR» (BitVec.sdiv (0 : BitVec 64) (3 : BitVec 64), 7) (fixture s 0 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (0 : BitVec 64) (3 : BitVec 64), 7) (fixture s 0 17 3) = _
 have numeric : (BitVec.sdiv (0 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_13_0
example (s : riscv_state) : «dfn'DIV» (0,1,0) (fixture s 0 18446744073709551615 3) = (let t := fixture s 0 18446744073709551615 3; t) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 0 18446744073709551615 3) else «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (0 : BitVec 64), 0) (fixture s 0 18446744073709551615 3)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 0 18446744073709551615 3) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_13_1
example (s : riscv_state) : «dfn'DIV» (1,1,0) (fixture s 0 18446744073709551615 3) = (let t := fixture s 0 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 0 18446744073709551615 3) else «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (0 : BitVec 64), 1) (fixture s 0 18446744073709551615 3)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 0 18446744073709551615 3) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_13_2
example (s : riscv_state) : «dfn'DIV» (2,1,0) (fixture s 0 18446744073709551615 3) = (let t := fixture s 0 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 0 18446744073709551615 3) else «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (0 : BitVec 64), 2) (fixture s 0 18446744073709551615 3)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 0 18446744073709551615 3) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_13_7
example (s : riscv_state) : «dfn'DIV» (7,1,0) (fixture s 0 18446744073709551615 3) = (let t := fixture s 0 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 0 18446744073709551615 3) else «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (0 : BitVec 64), 7) (fixture s 0 18446744073709551615 3)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 0 18446744073709551615 3) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_14_0
example (s : riscv_state) : «dfn'DIV» (0,1,1) (fixture s 0 9223372036854775808 2) = (let t := fixture s 0 9223372036854775808 2; t) := by
 change (if ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 0 9223372036854775808 2) else «write'GPR» (BitVec.sdiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 0) (fixture s 0 9223372036854775808 2)) = _
 have divisorZero : ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 0) (fixture s 0 9223372036854775808 2) = _
 have numeric : (BitVec.sdiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_14_1
example (s : riscv_state) : «dfn'DIV» (1,1,1) (fixture s 0 9223372036854775808 2) = (let t := fixture s 0 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 0 9223372036854775808 2) else «write'GPR» (BitVec.sdiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 1) (fixture s 0 9223372036854775808 2)) = _
 have divisorZero : ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 1) (fixture s 0 9223372036854775808 2) = _
 have numeric : (BitVec.sdiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_14_2
example (s : riscv_state) : «dfn'DIV» (2,1,1) (fixture s 0 9223372036854775808 2) = (let t := fixture s 0 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 0 9223372036854775808 2) else «write'GPR» (BitVec.sdiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 2) (fixture s 0 9223372036854775808 2)) = _
 have divisorZero : ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 2) (fixture s 0 9223372036854775808 2) = _
 have numeric : (BitVec.sdiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_0_14_7
example (s : riscv_state) : «dfn'DIV» (7,1,1) (fixture s 0 9223372036854775808 2) = (let t := fixture s 0 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 0 9223372036854775808 2) else «write'GPR» (BitVec.sdiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 7) (fixture s 0 9223372036854775808 2)) = _
 have divisorZero : ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 7) (fixture s 0 9223372036854775808 2) = _
 have numeric : (BitVec.sdiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_0_0
example (s : riscv_state) : «dfn'DIV» (0,1,2) (fixture s 2 0 0) = (let t := fixture s 2 0 0; t) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 2 0 0) else «write'GPR» (BitVec.sdiv (0 : BitVec 64) (0 : BitVec 64), 0) (fixture s 2 0 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 2 0 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_0_1
example (s : riscv_state) : «dfn'DIV» (1,1,2) (fixture s 2 0 0) = (let t := fixture s 2 0 0; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 2 0 0) else «write'GPR» (BitVec.sdiv (0 : BitVec 64) (0 : BitVec 64), 1) (fixture s 2 0 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 2 0 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_0_2
example (s : riscv_state) : «dfn'DIV» (2,1,2) (fixture s 2 0 0) = (let t := fixture s 2 0 0; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 2 0 0) else «write'GPR» (BitVec.sdiv (0 : BitVec 64) (0 : BitVec 64), 2) (fixture s 2 0 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 2 0 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_0_7
example (s : riscv_state) : «dfn'DIV» (7,1,2) (fixture s 2 0 0) = (let t := fixture s 2 0 0; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 2 0 0) else «write'GPR» (BitVec.sdiv (0 : BitVec 64) (0 : BitVec 64), 7) (fixture s 2 0 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 2 0 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_1_0
example (s : riscv_state) : «dfn'DIV» (0,1,2) (fixture s 2 17 0) = (let t := fixture s 2 17 0; t) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 2 17 0) else «write'GPR» (BitVec.sdiv (17 : BitVec 64) (0 : BitVec 64), 0) (fixture s 2 17 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 2 17 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_1_1
example (s : riscv_state) : «dfn'DIV» (1,1,2) (fixture s 2 17 0) = (let t := fixture s 2 17 0; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 2 17 0) else «write'GPR» (BitVec.sdiv (17 : BitVec 64) (0 : BitVec 64), 1) (fixture s 2 17 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 2 17 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_1_2
example (s : riscv_state) : «dfn'DIV» (2,1,2) (fixture s 2 17 0) = (let t := fixture s 2 17 0; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 2 17 0) else «write'GPR» (BitVec.sdiv (17 : BitVec 64) (0 : BitVec 64), 2) (fixture s 2 17 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 2 17 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_1_7
example (s : riscv_state) : «dfn'DIV» (7,1,2) (fixture s 2 17 0) = (let t := fixture s 2 17 0; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 2 17 0) else «write'GPR» (BitVec.sdiv (17 : BitVec 64) (0 : BitVec 64), 7) (fixture s 2 17 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 2 17 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_2_0
example (s : riscv_state) : «dfn'DIV» (0,1,2) (fixture s 2 18446744073709551615 0) = (let t := fixture s 2 18446744073709551615 0; t) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 2 18446744073709551615 0) else «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (0 : BitVec 64), 0) (fixture s 2 18446744073709551615 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 2 18446744073709551615 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_2_1
example (s : riscv_state) : «dfn'DIV» (1,1,2) (fixture s 2 18446744073709551615 0) = (let t := fixture s 2 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 2 18446744073709551615 0) else «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (0 : BitVec 64), 1) (fixture s 2 18446744073709551615 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 2 18446744073709551615 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_2_2
example (s : riscv_state) : «dfn'DIV» (2,1,2) (fixture s 2 18446744073709551615 0) = (let t := fixture s 2 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 2 18446744073709551615 0) else «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (0 : BitVec 64), 2) (fixture s 2 18446744073709551615 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 2 18446744073709551615 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_2_7
example (s : riscv_state) : «dfn'DIV» (7,1,2) (fixture s 2 18446744073709551615 0) = (let t := fixture s 2 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 2 18446744073709551615 0) else «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (0 : BitVec 64), 7) (fixture s 2 18446744073709551615 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 2 18446744073709551615 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_3_0
example (s : riscv_state) : «dfn'DIV» (0,1,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; t) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 2 17 3) else «write'GPR» (BitVec.sdiv (17 : BitVec 64) (3 : BitVec 64), 0) (fixture s 2 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (17 : BitVec 64) (3 : BitVec 64), 0) (fixture s 2 17 3) = _
 have numeric : (BitVec.sdiv (17 : BitVec 64) (3 : BitVec 64)) = (5 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_3_1
example (s : riscv_state) : «dfn'DIV» (1,1,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; {t with c_gpr := holUpdate 7 (holUpdate 1 5 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 2 17 3) else «write'GPR» (BitVec.sdiv (17 : BitVec 64) (3 : BitVec 64), 1) (fixture s 2 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (17 : BitVec 64) (3 : BitVec 64), 1) (fixture s 2 17 3) = _
 have numeric : (BitVec.sdiv (17 : BitVec 64) (3 : BitVec 64)) = (5 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_3_2
example (s : riscv_state) : «dfn'DIV» (2,1,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; {t with c_gpr := holUpdate 7 (holUpdate 2 5 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 2 17 3) else «write'GPR» (BitVec.sdiv (17 : BitVec 64) (3 : BitVec 64), 2) (fixture s 2 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (17 : BitVec 64) (3 : BitVec 64), 2) (fixture s 2 17 3) = _
 have numeric : (BitVec.sdiv (17 : BitVec 64) (3 : BitVec 64)) = (5 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_3_7
example (s : riscv_state) : «dfn'DIV» (7,1,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; {t with c_gpr := holUpdate 7 (holUpdate 7 5 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 2 17 3) else «write'GPR» (BitVec.sdiv (17 : BitVec 64) (3 : BitVec 64), 7) (fixture s 2 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (17 : BitVec 64) (3 : BitVec 64), 7) (fixture s 2 17 3) = _
 have numeric : (BitVec.sdiv (17 : BitVec 64) (3 : BitVec 64)) = (5 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_4_0
example (s : riscv_state) : «dfn'DIV» (0,1,2) (fixture s 2 18446744073709551599 3) = (let t := fixture s 2 18446744073709551599 3; t) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 2 18446744073709551599 3) else «write'GPR» (BitVec.sdiv (18446744073709551599 : BitVec 64) (3 : BitVec 64), 0) (fixture s 2 18446744073709551599 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (18446744073709551599 : BitVec 64) (3 : BitVec 64), 0) (fixture s 2 18446744073709551599 3) = _
 have numeric : (BitVec.sdiv (18446744073709551599 : BitVec 64) (3 : BitVec 64)) = (18446744073709551611 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_4_1
example (s : riscv_state) : «dfn'DIV» (1,1,2) (fixture s 2 18446744073709551599 3) = (let t := fixture s 2 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551611 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 2 18446744073709551599 3) else «write'GPR» (BitVec.sdiv (18446744073709551599 : BitVec 64) (3 : BitVec 64), 1) (fixture s 2 18446744073709551599 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (18446744073709551599 : BitVec 64) (3 : BitVec 64), 1) (fixture s 2 18446744073709551599 3) = _
 have numeric : (BitVec.sdiv (18446744073709551599 : BitVec 64) (3 : BitVec 64)) = (18446744073709551611 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_4_2
example (s : riscv_state) : «dfn'DIV» (2,1,2) (fixture s 2 18446744073709551599 3) = (let t := fixture s 2 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551611 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 2 18446744073709551599 3) else «write'GPR» (BitVec.sdiv (18446744073709551599 : BitVec 64) (3 : BitVec 64), 2) (fixture s 2 18446744073709551599 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (18446744073709551599 : BitVec 64) (3 : BitVec 64), 2) (fixture s 2 18446744073709551599 3) = _
 have numeric : (BitVec.sdiv (18446744073709551599 : BitVec 64) (3 : BitVec 64)) = (18446744073709551611 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_4_7
example (s : riscv_state) : «dfn'DIV» (7,1,2) (fixture s 2 18446744073709551599 3) = (let t := fixture s 2 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551611 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 2 18446744073709551599 3) else «write'GPR» (BitVec.sdiv (18446744073709551599 : BitVec 64) (3 : BitVec 64), 7) (fixture s 2 18446744073709551599 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (18446744073709551599 : BitVec 64) (3 : BitVec 64), 7) (fixture s 2 18446744073709551599 3) = _
 have numeric : (BitVec.sdiv (18446744073709551599 : BitVec 64) (3 : BitVec 64)) = (18446744073709551611 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_5_0
example (s : riscv_state) : «dfn'DIV» (0,1,2) (fixture s 2 17 18446744073709551613) = (let t := fixture s 2 17 18446744073709551613; t) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 2 17 18446744073709551613) else «write'GPR» (BitVec.sdiv (17 : BitVec 64) (18446744073709551613 : BitVec 64), 0) (fixture s 2 17 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (17 : BitVec 64) (18446744073709551613 : BitVec 64), 0) (fixture s 2 17 18446744073709551613) = _
 have numeric : (BitVec.sdiv (17 : BitVec 64) (18446744073709551613 : BitVec 64)) = (18446744073709551611 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_5_1
example (s : riscv_state) : «dfn'DIV» (1,1,2) (fixture s 2 17 18446744073709551613) = (let t := fixture s 2 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551611 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 2 17 18446744073709551613) else «write'GPR» (BitVec.sdiv (17 : BitVec 64) (18446744073709551613 : BitVec 64), 1) (fixture s 2 17 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (17 : BitVec 64) (18446744073709551613 : BitVec 64), 1) (fixture s 2 17 18446744073709551613) = _
 have numeric : (BitVec.sdiv (17 : BitVec 64) (18446744073709551613 : BitVec 64)) = (18446744073709551611 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_5_2
example (s : riscv_state) : «dfn'DIV» (2,1,2) (fixture s 2 17 18446744073709551613) = (let t := fixture s 2 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551611 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 2 17 18446744073709551613) else «write'GPR» (BitVec.sdiv (17 : BitVec 64) (18446744073709551613 : BitVec 64), 2) (fixture s 2 17 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (17 : BitVec 64) (18446744073709551613 : BitVec 64), 2) (fixture s 2 17 18446744073709551613) = _
 have numeric : (BitVec.sdiv (17 : BitVec 64) (18446744073709551613 : BitVec 64)) = (18446744073709551611 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_5_7
example (s : riscv_state) : «dfn'DIV» (7,1,2) (fixture s 2 17 18446744073709551613) = (let t := fixture s 2 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551611 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 2 17 18446744073709551613) else «write'GPR» (BitVec.sdiv (17 : BitVec 64) (18446744073709551613 : BitVec 64), 7) (fixture s 2 17 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (17 : BitVec 64) (18446744073709551613 : BitVec 64), 7) (fixture s 2 17 18446744073709551613) = _
 have numeric : (BitVec.sdiv (17 : BitVec 64) (18446744073709551613 : BitVec 64)) = (18446744073709551611 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_6_0
example (s : riscv_state) : «dfn'DIV» (0,1,2) (fixture s 2 18446744073709551599 18446744073709551613) = (let t := fixture s 2 18446744073709551599 18446744073709551613; t) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 2 18446744073709551599 18446744073709551613) else «write'GPR» (BitVec.sdiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 0) (fixture s 2 18446744073709551599 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 0) (fixture s 2 18446744073709551599 18446744073709551613) = _
 have numeric : (BitVec.sdiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64)) = (5 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_6_1
example (s : riscv_state) : «dfn'DIV» (1,1,2) (fixture s 2 18446744073709551599 18446744073709551613) = (let t := fixture s 2 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 1 5 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 2 18446744073709551599 18446744073709551613) else «write'GPR» (BitVec.sdiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 1) (fixture s 2 18446744073709551599 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 1) (fixture s 2 18446744073709551599 18446744073709551613) = _
 have numeric : (BitVec.sdiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64)) = (5 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_6_2
example (s : riscv_state) : «dfn'DIV» (2,1,2) (fixture s 2 18446744073709551599 18446744073709551613) = (let t := fixture s 2 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 2 5 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 2 18446744073709551599 18446744073709551613) else «write'GPR» (BitVec.sdiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 2) (fixture s 2 18446744073709551599 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 2) (fixture s 2 18446744073709551599 18446744073709551613) = _
 have numeric : (BitVec.sdiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64)) = (5 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_6_7
example (s : riscv_state) : «dfn'DIV» (7,1,2) (fixture s 2 18446744073709551599 18446744073709551613) = (let t := fixture s 2 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 7 5 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 2 18446744073709551599 18446744073709551613) else «write'GPR» (BitVec.sdiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 7) (fixture s 2 18446744073709551599 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 7) (fixture s 2 18446744073709551599 18446744073709551613) = _
 have numeric : (BitVec.sdiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64)) = (5 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_7_0
example (s : riscv_state) : «dfn'DIV» (0,1,2) (fixture s 2 9223372036854775808 18446744073709551615) = (let t := fixture s 2 9223372036854775808 18446744073709551615; t) := by
 change (if ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 2 9223372036854775808 18446744073709551615) else «write'GPR» (BitVec.sdiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 0) (fixture s 2 9223372036854775808 18446744073709551615)) = _
 have divisorZero : ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 0) (fixture s 2 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.sdiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64)) = (9223372036854775808 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_7_1
example (s : riscv_state) : «dfn'DIV» (1,1,2) (fixture s 2 9223372036854775808 18446744073709551615) = (let t := fixture s 2 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 2 9223372036854775808 18446744073709551615) else «write'GPR» (BitVec.sdiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 1) (fixture s 2 9223372036854775808 18446744073709551615)) = _
 have divisorZero : ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 1) (fixture s 2 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.sdiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64)) = (9223372036854775808 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_7_2
example (s : riscv_state) : «dfn'DIV» (2,1,2) (fixture s 2 9223372036854775808 18446744073709551615) = (let t := fixture s 2 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 2 9223372036854775808 18446744073709551615) else «write'GPR» (BitVec.sdiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 2) (fixture s 2 9223372036854775808 18446744073709551615)) = _
 have divisorZero : ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 2) (fixture s 2 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.sdiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64)) = (9223372036854775808 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_7_7
example (s : riscv_state) : «dfn'DIV» (7,1,2) (fixture s 2 9223372036854775808 18446744073709551615) = (let t := fixture s 2 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 2 9223372036854775808 18446744073709551615) else «write'GPR» (BitVec.sdiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 7) (fixture s 2 9223372036854775808 18446744073709551615)) = _
 have divisorZero : ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 7) (fixture s 2 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.sdiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64)) = (9223372036854775808 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_8_0
example (s : riscv_state) : «dfn'DIV» (0,1,2) (fixture s 2 2147483648 4294967295) = (let t := fixture s 2 2147483648 4294967295; t) := by
 change (if ((4294967295 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 2 2147483648 4294967295) else «write'GPR» (BitVec.sdiv (2147483648 : BitVec 64) (4294967295 : BitVec 64), 0) (fixture s 2 2147483648 4294967295)) = _
 have divisorZero : ((4294967295 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (2147483648 : BitVec 64) (4294967295 : BitVec 64), 0) (fixture s 2 2147483648 4294967295) = _
 have numeric : (BitVec.sdiv (2147483648 : BitVec 64) (4294967295 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_8_1
example (s : riscv_state) : «dfn'DIV» (1,1,2) (fixture s 2 2147483648 4294967295) = (let t := fixture s 2 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967295 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 2 2147483648 4294967295) else «write'GPR» (BitVec.sdiv (2147483648 : BitVec 64) (4294967295 : BitVec 64), 1) (fixture s 2 2147483648 4294967295)) = _
 have divisorZero : ((4294967295 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (2147483648 : BitVec 64) (4294967295 : BitVec 64), 1) (fixture s 2 2147483648 4294967295) = _
 have numeric : (BitVec.sdiv (2147483648 : BitVec 64) (4294967295 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_8_2
example (s : riscv_state) : «dfn'DIV» (2,1,2) (fixture s 2 2147483648 4294967295) = (let t := fixture s 2 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967295 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 2 2147483648 4294967295) else «write'GPR» (BitVec.sdiv (2147483648 : BitVec 64) (4294967295 : BitVec 64), 2) (fixture s 2 2147483648 4294967295)) = _
 have divisorZero : ((4294967295 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (2147483648 : BitVec 64) (4294967295 : BitVec 64), 2) (fixture s 2 2147483648 4294967295) = _
 have numeric : (BitVec.sdiv (2147483648 : BitVec 64) (4294967295 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_8_7
example (s : riscv_state) : «dfn'DIV» (7,1,2) (fixture s 2 2147483648 4294967295) = (let t := fixture s 2 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967295 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 2 2147483648 4294967295) else «write'GPR» (BitVec.sdiv (2147483648 : BitVec 64) (4294967295 : BitVec 64), 7) (fixture s 2 2147483648 4294967295)) = _
 have divisorZero : ((4294967295 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (2147483648 : BitVec 64) (4294967295 : BitVec 64), 7) (fixture s 2 2147483648 4294967295) = _
 have numeric : (BitVec.sdiv (2147483648 : BitVec 64) (4294967295 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_9_0
example (s : riscv_state) : «dfn'DIV» (0,1,2) (fixture s 2 4294967313 4294967296) = (let t := fixture s 2 4294967313 4294967296; t) := by
 change (if ((4294967296 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 2 4294967313 4294967296) else «write'GPR» (BitVec.sdiv (4294967313 : BitVec 64) (4294967296 : BitVec 64), 0) (fixture s 2 4294967313 4294967296)) = _
 have divisorZero : ((4294967296 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (4294967313 : BitVec 64) (4294967296 : BitVec 64), 0) (fixture s 2 4294967313 4294967296) = _
 have numeric : (BitVec.sdiv (4294967313 : BitVec 64) (4294967296 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_9_1
example (s : riscv_state) : «dfn'DIV» (1,1,2) (fixture s 2 4294967313 4294967296) = (let t := fixture s 2 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967296 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 2 4294967313 4294967296) else «write'GPR» (BitVec.sdiv (4294967313 : BitVec 64) (4294967296 : BitVec 64), 1) (fixture s 2 4294967313 4294967296)) = _
 have divisorZero : ((4294967296 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (4294967313 : BitVec 64) (4294967296 : BitVec 64), 1) (fixture s 2 4294967313 4294967296) = _
 have numeric : (BitVec.sdiv (4294967313 : BitVec 64) (4294967296 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_9_2
example (s : riscv_state) : «dfn'DIV» (2,1,2) (fixture s 2 4294967313 4294967296) = (let t := fixture s 2 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967296 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 2 4294967313 4294967296) else «write'GPR» (BitVec.sdiv (4294967313 : BitVec 64) (4294967296 : BitVec 64), 2) (fixture s 2 4294967313 4294967296)) = _
 have divisorZero : ((4294967296 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (4294967313 : BitVec 64) (4294967296 : BitVec 64), 2) (fixture s 2 4294967313 4294967296) = _
 have numeric : (BitVec.sdiv (4294967313 : BitVec 64) (4294967296 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_9_7
example (s : riscv_state) : «dfn'DIV» (7,1,2) (fixture s 2 4294967313 4294967296) = (let t := fixture s 2 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967296 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 2 4294967313 4294967296) else «write'GPR» (BitVec.sdiv (4294967313 : BitVec 64) (4294967296 : BitVec 64), 7) (fixture s 2 4294967313 4294967296)) = _
 have divisorZero : ((4294967296 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (4294967313 : BitVec 64) (4294967296 : BitVec 64), 7) (fixture s 2 4294967313 4294967296) = _
 have numeric : (BitVec.sdiv (4294967313 : BitVec 64) (4294967296 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_10_0
example (s : riscv_state) : «dfn'DIV» (0,1,2) (fixture s 2 18446744073709551615 2) = (let t := fixture s 2 18446744073709551615 2; t) := by
 change (if ((2 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 2 18446744073709551615 2) else «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (2 : BitVec 64), 0) (fixture s 2 18446744073709551615 2)) = _
 have divisorZero : ((2 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (2 : BitVec 64), 0) (fixture s 2 18446744073709551615 2) = _
 have numeric : (BitVec.sdiv (18446744073709551615 : BitVec 64) (2 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_10_1
example (s : riscv_state) : «dfn'DIV» (1,1,2) (fixture s 2 18446744073709551615 2) = (let t := fixture s 2 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((2 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 2 18446744073709551615 2) else «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (2 : BitVec 64), 1) (fixture s 2 18446744073709551615 2)) = _
 have divisorZero : ((2 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (2 : BitVec 64), 1) (fixture s 2 18446744073709551615 2) = _
 have numeric : (BitVec.sdiv (18446744073709551615 : BitVec 64) (2 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_10_2
example (s : riscv_state) : «dfn'DIV» (2,1,2) (fixture s 2 18446744073709551615 2) = (let t := fixture s 2 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((2 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 2 18446744073709551615 2) else «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (2 : BitVec 64), 2) (fixture s 2 18446744073709551615 2)) = _
 have divisorZero : ((2 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (2 : BitVec 64), 2) (fixture s 2 18446744073709551615 2) = _
 have numeric : (BitVec.sdiv (18446744073709551615 : BitVec 64) (2 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_10_7
example (s : riscv_state) : «dfn'DIV» (7,1,2) (fixture s 2 18446744073709551615 2) = (let t := fixture s 2 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((2 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 2 18446744073709551615 2) else «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (2 : BitVec 64), 7) (fixture s 2 18446744073709551615 2)) = _
 have divisorZero : ((2 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (2 : BitVec 64), 7) (fixture s 2 18446744073709551615 2) = _
 have numeric : (BitVec.sdiv (18446744073709551615 : BitVec 64) (2 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_11_0
example (s : riscv_state) : «dfn'DIV» (0,1,2) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; t) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 2 18446744073709551615 3) else «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (3 : BitVec 64), 0) (fixture s 2 18446744073709551615 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (3 : BitVec 64), 0) (fixture s 2 18446744073709551615 3) = _
 have numeric : (BitVec.sdiv (18446744073709551615 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_11_1
example (s : riscv_state) : «dfn'DIV» (1,1,2) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 2 18446744073709551615 3) else «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (3 : BitVec 64), 1) (fixture s 2 18446744073709551615 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (3 : BitVec 64), 1) (fixture s 2 18446744073709551615 3) = _
 have numeric : (BitVec.sdiv (18446744073709551615 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_11_2
example (s : riscv_state) : «dfn'DIV» (2,1,2) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 2 18446744073709551615 3) else «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (3 : BitVec 64), 2) (fixture s 2 18446744073709551615 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (3 : BitVec 64), 2) (fixture s 2 18446744073709551615 3) = _
 have numeric : (BitVec.sdiv (18446744073709551615 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_11_7
example (s : riscv_state) : «dfn'DIV» (7,1,2) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 2 18446744073709551615 3) else «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (3 : BitVec 64), 7) (fixture s 2 18446744073709551615 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (3 : BitVec 64), 7) (fixture s 2 18446744073709551615 3) = _
 have numeric : (BitVec.sdiv (18446744073709551615 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_12_0
example (s : riscv_state) : «dfn'DIV» (0,0,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; t) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 2 17 3) else «write'GPR» (BitVec.sdiv (0 : BitVec 64) (3 : BitVec 64), 0) (fixture s 2 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (0 : BitVec 64) (3 : BitVec 64), 0) (fixture s 2 17 3) = _
 have numeric : (BitVec.sdiv (0 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_12_1
example (s : riscv_state) : «dfn'DIV» (1,0,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 2 17 3) else «write'GPR» (BitVec.sdiv (0 : BitVec 64) (3 : BitVec 64), 1) (fixture s 2 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (0 : BitVec 64) (3 : BitVec 64), 1) (fixture s 2 17 3) = _
 have numeric : (BitVec.sdiv (0 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_12_2
example (s : riscv_state) : «dfn'DIV» (2,0,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 2 17 3) else «write'GPR» (BitVec.sdiv (0 : BitVec 64) (3 : BitVec 64), 2) (fixture s 2 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (0 : BitVec 64) (3 : BitVec 64), 2) (fixture s 2 17 3) = _
 have numeric : (BitVec.sdiv (0 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_12_7
example (s : riscv_state) : «dfn'DIV» (7,0,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 2 17 3) else «write'GPR» (BitVec.sdiv (0 : BitVec 64) (3 : BitVec 64), 7) (fixture s 2 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (0 : BitVec 64) (3 : BitVec 64), 7) (fixture s 2 17 3) = _
 have numeric : (BitVec.sdiv (0 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_13_0
example (s : riscv_state) : «dfn'DIV» (0,1,0) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; t) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 2 18446744073709551615 3) else «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (0 : BitVec 64), 0) (fixture s 2 18446744073709551615 3)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 2 18446744073709551615 3) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_13_1
example (s : riscv_state) : «dfn'DIV» (1,1,0) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 2 18446744073709551615 3) else «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (0 : BitVec 64), 1) (fixture s 2 18446744073709551615 3)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 2 18446744073709551615 3) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_13_2
example (s : riscv_state) : «dfn'DIV» (2,1,0) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 2 18446744073709551615 3) else «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (0 : BitVec 64), 2) (fixture s 2 18446744073709551615 3)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 2 18446744073709551615 3) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_13_7
example (s : riscv_state) : «dfn'DIV» (7,1,0) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 2 18446744073709551615 3) else «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (0 : BitVec 64), 7) (fixture s 2 18446744073709551615 3)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 2 18446744073709551615 3) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_14_0
example (s : riscv_state) : «dfn'DIV» (0,1,1) (fixture s 2 9223372036854775808 2) = (let t := fixture s 2 9223372036854775808 2; t) := by
 change (if ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 2 9223372036854775808 2) else «write'GPR» (BitVec.sdiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 0) (fixture s 2 9223372036854775808 2)) = _
 have divisorZero : ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 0) (fixture s 2 9223372036854775808 2) = _
 have numeric : (BitVec.sdiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_14_1
example (s : riscv_state) : «dfn'DIV» (1,1,1) (fixture s 2 9223372036854775808 2) = (let t := fixture s 2 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 2 9223372036854775808 2) else «write'GPR» (BitVec.sdiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 1) (fixture s 2 9223372036854775808 2)) = _
 have divisorZero : ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 1) (fixture s 2 9223372036854775808 2) = _
 have numeric : (BitVec.sdiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_14_2
example (s : riscv_state) : «dfn'DIV» (2,1,1) (fixture s 2 9223372036854775808 2) = (let t := fixture s 2 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 2 9223372036854775808 2) else «write'GPR» (BitVec.sdiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 2) (fixture s 2 9223372036854775808 2)) = _
 have divisorZero : ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 2) (fixture s 2 9223372036854775808 2) = _
 have numeric : (BitVec.sdiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_2_14_7
example (s : riscv_state) : «dfn'DIV» (7,1,1) (fixture s 2 9223372036854775808 2) = (let t := fixture s 2 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 2 9223372036854775808 2) else «write'GPR» (BitVec.sdiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 7) (fixture s 2 9223372036854775808 2)) = _
 have divisorZero : ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 7) (fixture s 2 9223372036854775808 2) = _
 have numeric : (BitVec.sdiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_0_0
example (s : riscv_state) : «dfn'DIV» (0,1,2) (fixture s 3 0 0) = (let t := fixture s 3 0 0; t) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 3 0 0) else «write'GPR» (BitVec.sdiv (0 : BitVec 64) (0 : BitVec 64), 0) (fixture s 3 0 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 3 0 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_0_1
example (s : riscv_state) : «dfn'DIV» (1,1,2) (fixture s 3 0 0) = (let t := fixture s 3 0 0; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 3 0 0) else «write'GPR» (BitVec.sdiv (0 : BitVec 64) (0 : BitVec 64), 1) (fixture s 3 0 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 3 0 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_0_2
example (s : riscv_state) : «dfn'DIV» (2,1,2) (fixture s 3 0 0) = (let t := fixture s 3 0 0; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 3 0 0) else «write'GPR» (BitVec.sdiv (0 : BitVec 64) (0 : BitVec 64), 2) (fixture s 3 0 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 3 0 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_0_7
example (s : riscv_state) : «dfn'DIV» (7,1,2) (fixture s 3 0 0) = (let t := fixture s 3 0 0; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 3 0 0) else «write'GPR» (BitVec.sdiv (0 : BitVec 64) (0 : BitVec 64), 7) (fixture s 3 0 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 3 0 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_1_0
example (s : riscv_state) : «dfn'DIV» (0,1,2) (fixture s 3 17 0) = (let t := fixture s 3 17 0; t) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 3 17 0) else «write'GPR» (BitVec.sdiv (17 : BitVec 64) (0 : BitVec 64), 0) (fixture s 3 17 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 3 17 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_1_1
example (s : riscv_state) : «dfn'DIV» (1,1,2) (fixture s 3 17 0) = (let t := fixture s 3 17 0; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 3 17 0) else «write'GPR» (BitVec.sdiv (17 : BitVec 64) (0 : BitVec 64), 1) (fixture s 3 17 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 3 17 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_1_2
example (s : riscv_state) : «dfn'DIV» (2,1,2) (fixture s 3 17 0) = (let t := fixture s 3 17 0; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 3 17 0) else «write'GPR» (BitVec.sdiv (17 : BitVec 64) (0 : BitVec 64), 2) (fixture s 3 17 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 3 17 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_1_7
example (s : riscv_state) : «dfn'DIV» (7,1,2) (fixture s 3 17 0) = (let t := fixture s 3 17 0; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 3 17 0) else «write'GPR» (BitVec.sdiv (17 : BitVec 64) (0 : BitVec 64), 7) (fixture s 3 17 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 3 17 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_2_0
example (s : riscv_state) : «dfn'DIV» (0,1,2) (fixture s 3 18446744073709551615 0) = (let t := fixture s 3 18446744073709551615 0; t) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 3 18446744073709551615 0) else «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (0 : BitVec 64), 0) (fixture s 3 18446744073709551615 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 3 18446744073709551615 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_2_1
example (s : riscv_state) : «dfn'DIV» (1,1,2) (fixture s 3 18446744073709551615 0) = (let t := fixture s 3 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 3 18446744073709551615 0) else «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (0 : BitVec 64), 1) (fixture s 3 18446744073709551615 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 3 18446744073709551615 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_2_2
example (s : riscv_state) : «dfn'DIV» (2,1,2) (fixture s 3 18446744073709551615 0) = (let t := fixture s 3 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 3 18446744073709551615 0) else «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (0 : BitVec 64), 2) (fixture s 3 18446744073709551615 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 3 18446744073709551615 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_2_7
example (s : riscv_state) : «dfn'DIV» (7,1,2) (fixture s 3 18446744073709551615 0) = (let t := fixture s 3 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 3 18446744073709551615 0) else «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (0 : BitVec 64), 7) (fixture s 3 18446744073709551615 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 3 18446744073709551615 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_3_0
example (s : riscv_state) : «dfn'DIV» (0,1,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; t) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 3 17 3) else «write'GPR» (BitVec.sdiv (17 : BitVec 64) (3 : BitVec 64), 0) (fixture s 3 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (17 : BitVec 64) (3 : BitVec 64), 0) (fixture s 3 17 3) = _
 have numeric : (BitVec.sdiv (17 : BitVec 64) (3 : BitVec 64)) = (5 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_3_1
example (s : riscv_state) : «dfn'DIV» (1,1,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; {t with c_gpr := holUpdate 7 (holUpdate 1 5 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 3 17 3) else «write'GPR» (BitVec.sdiv (17 : BitVec 64) (3 : BitVec 64), 1) (fixture s 3 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (17 : BitVec 64) (3 : BitVec 64), 1) (fixture s 3 17 3) = _
 have numeric : (BitVec.sdiv (17 : BitVec 64) (3 : BitVec 64)) = (5 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_3_2
example (s : riscv_state) : «dfn'DIV» (2,1,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; {t with c_gpr := holUpdate 7 (holUpdate 2 5 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 3 17 3) else «write'GPR» (BitVec.sdiv (17 : BitVec 64) (3 : BitVec 64), 2) (fixture s 3 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (17 : BitVec 64) (3 : BitVec 64), 2) (fixture s 3 17 3) = _
 have numeric : (BitVec.sdiv (17 : BitVec 64) (3 : BitVec 64)) = (5 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_3_7
example (s : riscv_state) : «dfn'DIV» (7,1,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; {t with c_gpr := holUpdate 7 (holUpdate 7 5 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 3 17 3) else «write'GPR» (BitVec.sdiv (17 : BitVec 64) (3 : BitVec 64), 7) (fixture s 3 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (17 : BitVec 64) (3 : BitVec 64), 7) (fixture s 3 17 3) = _
 have numeric : (BitVec.sdiv (17 : BitVec 64) (3 : BitVec 64)) = (5 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_4_0
example (s : riscv_state) : «dfn'DIV» (0,1,2) (fixture s 3 18446744073709551599 3) = (let t := fixture s 3 18446744073709551599 3; t) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 3 18446744073709551599 3) else «write'GPR» (BitVec.sdiv (18446744073709551599 : BitVec 64) (3 : BitVec 64), 0) (fixture s 3 18446744073709551599 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (18446744073709551599 : BitVec 64) (3 : BitVec 64), 0) (fixture s 3 18446744073709551599 3) = _
 have numeric : (BitVec.sdiv (18446744073709551599 : BitVec 64) (3 : BitVec 64)) = (18446744073709551611 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_4_1
example (s : riscv_state) : «dfn'DIV» (1,1,2) (fixture s 3 18446744073709551599 3) = (let t := fixture s 3 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551611 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 3 18446744073709551599 3) else «write'GPR» (BitVec.sdiv (18446744073709551599 : BitVec 64) (3 : BitVec 64), 1) (fixture s 3 18446744073709551599 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (18446744073709551599 : BitVec 64) (3 : BitVec 64), 1) (fixture s 3 18446744073709551599 3) = _
 have numeric : (BitVec.sdiv (18446744073709551599 : BitVec 64) (3 : BitVec 64)) = (18446744073709551611 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_4_2
example (s : riscv_state) : «dfn'DIV» (2,1,2) (fixture s 3 18446744073709551599 3) = (let t := fixture s 3 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551611 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 3 18446744073709551599 3) else «write'GPR» (BitVec.sdiv (18446744073709551599 : BitVec 64) (3 : BitVec 64), 2) (fixture s 3 18446744073709551599 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (18446744073709551599 : BitVec 64) (3 : BitVec 64), 2) (fixture s 3 18446744073709551599 3) = _
 have numeric : (BitVec.sdiv (18446744073709551599 : BitVec 64) (3 : BitVec 64)) = (18446744073709551611 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_4_7
example (s : riscv_state) : «dfn'DIV» (7,1,2) (fixture s 3 18446744073709551599 3) = (let t := fixture s 3 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551611 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 3 18446744073709551599 3) else «write'GPR» (BitVec.sdiv (18446744073709551599 : BitVec 64) (3 : BitVec 64), 7) (fixture s 3 18446744073709551599 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (18446744073709551599 : BitVec 64) (3 : BitVec 64), 7) (fixture s 3 18446744073709551599 3) = _
 have numeric : (BitVec.sdiv (18446744073709551599 : BitVec 64) (3 : BitVec 64)) = (18446744073709551611 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_5_0
example (s : riscv_state) : «dfn'DIV» (0,1,2) (fixture s 3 17 18446744073709551613) = (let t := fixture s 3 17 18446744073709551613; t) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 3 17 18446744073709551613) else «write'GPR» (BitVec.sdiv (17 : BitVec 64) (18446744073709551613 : BitVec 64), 0) (fixture s 3 17 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (17 : BitVec 64) (18446744073709551613 : BitVec 64), 0) (fixture s 3 17 18446744073709551613) = _
 have numeric : (BitVec.sdiv (17 : BitVec 64) (18446744073709551613 : BitVec 64)) = (18446744073709551611 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_5_1
example (s : riscv_state) : «dfn'DIV» (1,1,2) (fixture s 3 17 18446744073709551613) = (let t := fixture s 3 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551611 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 3 17 18446744073709551613) else «write'GPR» (BitVec.sdiv (17 : BitVec 64) (18446744073709551613 : BitVec 64), 1) (fixture s 3 17 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (17 : BitVec 64) (18446744073709551613 : BitVec 64), 1) (fixture s 3 17 18446744073709551613) = _
 have numeric : (BitVec.sdiv (17 : BitVec 64) (18446744073709551613 : BitVec 64)) = (18446744073709551611 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_5_2
example (s : riscv_state) : «dfn'DIV» (2,1,2) (fixture s 3 17 18446744073709551613) = (let t := fixture s 3 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551611 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 3 17 18446744073709551613) else «write'GPR» (BitVec.sdiv (17 : BitVec 64) (18446744073709551613 : BitVec 64), 2) (fixture s 3 17 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (17 : BitVec 64) (18446744073709551613 : BitVec 64), 2) (fixture s 3 17 18446744073709551613) = _
 have numeric : (BitVec.sdiv (17 : BitVec 64) (18446744073709551613 : BitVec 64)) = (18446744073709551611 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_5_7
example (s : riscv_state) : «dfn'DIV» (7,1,2) (fixture s 3 17 18446744073709551613) = (let t := fixture s 3 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551611 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 3 17 18446744073709551613) else «write'GPR» (BitVec.sdiv (17 : BitVec 64) (18446744073709551613 : BitVec 64), 7) (fixture s 3 17 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (17 : BitVec 64) (18446744073709551613 : BitVec 64), 7) (fixture s 3 17 18446744073709551613) = _
 have numeric : (BitVec.sdiv (17 : BitVec 64) (18446744073709551613 : BitVec 64)) = (18446744073709551611 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_6_0
example (s : riscv_state) : «dfn'DIV» (0,1,2) (fixture s 3 18446744073709551599 18446744073709551613) = (let t := fixture s 3 18446744073709551599 18446744073709551613; t) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 3 18446744073709551599 18446744073709551613) else «write'GPR» (BitVec.sdiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 0) (fixture s 3 18446744073709551599 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 0) (fixture s 3 18446744073709551599 18446744073709551613) = _
 have numeric : (BitVec.sdiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64)) = (5 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_6_1
example (s : riscv_state) : «dfn'DIV» (1,1,2) (fixture s 3 18446744073709551599 18446744073709551613) = (let t := fixture s 3 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 1 5 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 3 18446744073709551599 18446744073709551613) else «write'GPR» (BitVec.sdiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 1) (fixture s 3 18446744073709551599 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 1) (fixture s 3 18446744073709551599 18446744073709551613) = _
 have numeric : (BitVec.sdiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64)) = (5 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_6_2
example (s : riscv_state) : «dfn'DIV» (2,1,2) (fixture s 3 18446744073709551599 18446744073709551613) = (let t := fixture s 3 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 2 5 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 3 18446744073709551599 18446744073709551613) else «write'GPR» (BitVec.sdiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 2) (fixture s 3 18446744073709551599 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 2) (fixture s 3 18446744073709551599 18446744073709551613) = _
 have numeric : (BitVec.sdiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64)) = (5 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_6_7
example (s : riscv_state) : «dfn'DIV» (7,1,2) (fixture s 3 18446744073709551599 18446744073709551613) = (let t := fixture s 3 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 7 5 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 3 18446744073709551599 18446744073709551613) else «write'GPR» (BitVec.sdiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 7) (fixture s 3 18446744073709551599 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 7) (fixture s 3 18446744073709551599 18446744073709551613) = _
 have numeric : (BitVec.sdiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64)) = (5 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_7_0
example (s : riscv_state) : «dfn'DIV» (0,1,2) (fixture s 3 9223372036854775808 18446744073709551615) = (let t := fixture s 3 9223372036854775808 18446744073709551615; t) := by
 change (if ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 3 9223372036854775808 18446744073709551615) else «write'GPR» (BitVec.sdiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 0) (fixture s 3 9223372036854775808 18446744073709551615)) = _
 have divisorZero : ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 0) (fixture s 3 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.sdiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64)) = (9223372036854775808 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_7_1
example (s : riscv_state) : «dfn'DIV» (1,1,2) (fixture s 3 9223372036854775808 18446744073709551615) = (let t := fixture s 3 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 3 9223372036854775808 18446744073709551615) else «write'GPR» (BitVec.sdiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 1) (fixture s 3 9223372036854775808 18446744073709551615)) = _
 have divisorZero : ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 1) (fixture s 3 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.sdiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64)) = (9223372036854775808 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_7_2
example (s : riscv_state) : «dfn'DIV» (2,1,2) (fixture s 3 9223372036854775808 18446744073709551615) = (let t := fixture s 3 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 3 9223372036854775808 18446744073709551615) else «write'GPR» (BitVec.sdiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 2) (fixture s 3 9223372036854775808 18446744073709551615)) = _
 have divisorZero : ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 2) (fixture s 3 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.sdiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64)) = (9223372036854775808 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_7_7
example (s : riscv_state) : «dfn'DIV» (7,1,2) (fixture s 3 9223372036854775808 18446744073709551615) = (let t := fixture s 3 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 3 9223372036854775808 18446744073709551615) else «write'GPR» (BitVec.sdiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 7) (fixture s 3 9223372036854775808 18446744073709551615)) = _
 have divisorZero : ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 7) (fixture s 3 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.sdiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64)) = (9223372036854775808 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_8_0
example (s : riscv_state) : «dfn'DIV» (0,1,2) (fixture s 3 2147483648 4294967295) = (let t := fixture s 3 2147483648 4294967295; t) := by
 change (if ((4294967295 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 3 2147483648 4294967295) else «write'GPR» (BitVec.sdiv (2147483648 : BitVec 64) (4294967295 : BitVec 64), 0) (fixture s 3 2147483648 4294967295)) = _
 have divisorZero : ((4294967295 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (2147483648 : BitVec 64) (4294967295 : BitVec 64), 0) (fixture s 3 2147483648 4294967295) = _
 have numeric : (BitVec.sdiv (2147483648 : BitVec 64) (4294967295 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_8_1
example (s : riscv_state) : «dfn'DIV» (1,1,2) (fixture s 3 2147483648 4294967295) = (let t := fixture s 3 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967295 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 3 2147483648 4294967295) else «write'GPR» (BitVec.sdiv (2147483648 : BitVec 64) (4294967295 : BitVec 64), 1) (fixture s 3 2147483648 4294967295)) = _
 have divisorZero : ((4294967295 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (2147483648 : BitVec 64) (4294967295 : BitVec 64), 1) (fixture s 3 2147483648 4294967295) = _
 have numeric : (BitVec.sdiv (2147483648 : BitVec 64) (4294967295 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_8_2
example (s : riscv_state) : «dfn'DIV» (2,1,2) (fixture s 3 2147483648 4294967295) = (let t := fixture s 3 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967295 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 3 2147483648 4294967295) else «write'GPR» (BitVec.sdiv (2147483648 : BitVec 64) (4294967295 : BitVec 64), 2) (fixture s 3 2147483648 4294967295)) = _
 have divisorZero : ((4294967295 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (2147483648 : BitVec 64) (4294967295 : BitVec 64), 2) (fixture s 3 2147483648 4294967295) = _
 have numeric : (BitVec.sdiv (2147483648 : BitVec 64) (4294967295 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_8_7
example (s : riscv_state) : «dfn'DIV» (7,1,2) (fixture s 3 2147483648 4294967295) = (let t := fixture s 3 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967295 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 3 2147483648 4294967295) else «write'GPR» (BitVec.sdiv (2147483648 : BitVec 64) (4294967295 : BitVec 64), 7) (fixture s 3 2147483648 4294967295)) = _
 have divisorZero : ((4294967295 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (2147483648 : BitVec 64) (4294967295 : BitVec 64), 7) (fixture s 3 2147483648 4294967295) = _
 have numeric : (BitVec.sdiv (2147483648 : BitVec 64) (4294967295 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_9_0
example (s : riscv_state) : «dfn'DIV» (0,1,2) (fixture s 3 4294967313 4294967296) = (let t := fixture s 3 4294967313 4294967296; t) := by
 change (if ((4294967296 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 3 4294967313 4294967296) else «write'GPR» (BitVec.sdiv (4294967313 : BitVec 64) (4294967296 : BitVec 64), 0) (fixture s 3 4294967313 4294967296)) = _
 have divisorZero : ((4294967296 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (4294967313 : BitVec 64) (4294967296 : BitVec 64), 0) (fixture s 3 4294967313 4294967296) = _
 have numeric : (BitVec.sdiv (4294967313 : BitVec 64) (4294967296 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_9_1
example (s : riscv_state) : «dfn'DIV» (1,1,2) (fixture s 3 4294967313 4294967296) = (let t := fixture s 3 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967296 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 3 4294967313 4294967296) else «write'GPR» (BitVec.sdiv (4294967313 : BitVec 64) (4294967296 : BitVec 64), 1) (fixture s 3 4294967313 4294967296)) = _
 have divisorZero : ((4294967296 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (4294967313 : BitVec 64) (4294967296 : BitVec 64), 1) (fixture s 3 4294967313 4294967296) = _
 have numeric : (BitVec.sdiv (4294967313 : BitVec 64) (4294967296 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_9_2
example (s : riscv_state) : «dfn'DIV» (2,1,2) (fixture s 3 4294967313 4294967296) = (let t := fixture s 3 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967296 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 3 4294967313 4294967296) else «write'GPR» (BitVec.sdiv (4294967313 : BitVec 64) (4294967296 : BitVec 64), 2) (fixture s 3 4294967313 4294967296)) = _
 have divisorZero : ((4294967296 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (4294967313 : BitVec 64) (4294967296 : BitVec 64), 2) (fixture s 3 4294967313 4294967296) = _
 have numeric : (BitVec.sdiv (4294967313 : BitVec 64) (4294967296 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_9_7
example (s : riscv_state) : «dfn'DIV» (7,1,2) (fixture s 3 4294967313 4294967296) = (let t := fixture s 3 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967296 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 3 4294967313 4294967296) else «write'GPR» (BitVec.sdiv (4294967313 : BitVec 64) (4294967296 : BitVec 64), 7) (fixture s 3 4294967313 4294967296)) = _
 have divisorZero : ((4294967296 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (4294967313 : BitVec 64) (4294967296 : BitVec 64), 7) (fixture s 3 4294967313 4294967296) = _
 have numeric : (BitVec.sdiv (4294967313 : BitVec 64) (4294967296 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_10_0
example (s : riscv_state) : «dfn'DIV» (0,1,2) (fixture s 3 18446744073709551615 2) = (let t := fixture s 3 18446744073709551615 2; t) := by
 change (if ((2 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 3 18446744073709551615 2) else «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (2 : BitVec 64), 0) (fixture s 3 18446744073709551615 2)) = _
 have divisorZero : ((2 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (2 : BitVec 64), 0) (fixture s 3 18446744073709551615 2) = _
 have numeric : (BitVec.sdiv (18446744073709551615 : BitVec 64) (2 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_10_1
example (s : riscv_state) : «dfn'DIV» (1,1,2) (fixture s 3 18446744073709551615 2) = (let t := fixture s 3 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((2 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 3 18446744073709551615 2) else «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (2 : BitVec 64), 1) (fixture s 3 18446744073709551615 2)) = _
 have divisorZero : ((2 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (2 : BitVec 64), 1) (fixture s 3 18446744073709551615 2) = _
 have numeric : (BitVec.sdiv (18446744073709551615 : BitVec 64) (2 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_10_2
example (s : riscv_state) : «dfn'DIV» (2,1,2) (fixture s 3 18446744073709551615 2) = (let t := fixture s 3 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((2 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 3 18446744073709551615 2) else «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (2 : BitVec 64), 2) (fixture s 3 18446744073709551615 2)) = _
 have divisorZero : ((2 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (2 : BitVec 64), 2) (fixture s 3 18446744073709551615 2) = _
 have numeric : (BitVec.sdiv (18446744073709551615 : BitVec 64) (2 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_10_7
example (s : riscv_state) : «dfn'DIV» (7,1,2) (fixture s 3 18446744073709551615 2) = (let t := fixture s 3 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((2 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 3 18446744073709551615 2) else «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (2 : BitVec 64), 7) (fixture s 3 18446744073709551615 2)) = _
 have divisorZero : ((2 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (2 : BitVec 64), 7) (fixture s 3 18446744073709551615 2) = _
 have numeric : (BitVec.sdiv (18446744073709551615 : BitVec 64) (2 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_11_0
example (s : riscv_state) : «dfn'DIV» (0,1,2) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; t) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 3 18446744073709551615 3) else «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (3 : BitVec 64), 0) (fixture s 3 18446744073709551615 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (3 : BitVec 64), 0) (fixture s 3 18446744073709551615 3) = _
 have numeric : (BitVec.sdiv (18446744073709551615 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_11_1
example (s : riscv_state) : «dfn'DIV» (1,1,2) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 3 18446744073709551615 3) else «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (3 : BitVec 64), 1) (fixture s 3 18446744073709551615 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (3 : BitVec 64), 1) (fixture s 3 18446744073709551615 3) = _
 have numeric : (BitVec.sdiv (18446744073709551615 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_11_2
example (s : riscv_state) : «dfn'DIV» (2,1,2) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 3 18446744073709551615 3) else «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (3 : BitVec 64), 2) (fixture s 3 18446744073709551615 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (3 : BitVec 64), 2) (fixture s 3 18446744073709551615 3) = _
 have numeric : (BitVec.sdiv (18446744073709551615 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_11_7
example (s : riscv_state) : «dfn'DIV» (7,1,2) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 3 18446744073709551615 3) else «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (3 : BitVec 64), 7) (fixture s 3 18446744073709551615 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (3 : BitVec 64), 7) (fixture s 3 18446744073709551615 3) = _
 have numeric : (BitVec.sdiv (18446744073709551615 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_12_0
example (s : riscv_state) : «dfn'DIV» (0,0,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; t) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 3 17 3) else «write'GPR» (BitVec.sdiv (0 : BitVec 64) (3 : BitVec 64), 0) (fixture s 3 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (0 : BitVec 64) (3 : BitVec 64), 0) (fixture s 3 17 3) = _
 have numeric : (BitVec.sdiv (0 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_12_1
example (s : riscv_state) : «dfn'DIV» (1,0,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 3 17 3) else «write'GPR» (BitVec.sdiv (0 : BitVec 64) (3 : BitVec 64), 1) (fixture s 3 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (0 : BitVec 64) (3 : BitVec 64), 1) (fixture s 3 17 3) = _
 have numeric : (BitVec.sdiv (0 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_12_2
example (s : riscv_state) : «dfn'DIV» (2,0,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 3 17 3) else «write'GPR» (BitVec.sdiv (0 : BitVec 64) (3 : BitVec 64), 2) (fixture s 3 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (0 : BitVec 64) (3 : BitVec 64), 2) (fixture s 3 17 3) = _
 have numeric : (BitVec.sdiv (0 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_12_7
example (s : riscv_state) : «dfn'DIV» (7,0,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 3 17 3) else «write'GPR» (BitVec.sdiv (0 : BitVec 64) (3 : BitVec 64), 7) (fixture s 3 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (0 : BitVec 64) (3 : BitVec 64), 7) (fixture s 3 17 3) = _
 have numeric : (BitVec.sdiv (0 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_13_0
example (s : riscv_state) : «dfn'DIV» (0,1,0) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; t) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 3 18446744073709551615 3) else «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (0 : BitVec 64), 0) (fixture s 3 18446744073709551615 3)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 3 18446744073709551615 3) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_13_1
example (s : riscv_state) : «dfn'DIV» (1,1,0) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 3 18446744073709551615 3) else «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (0 : BitVec 64), 1) (fixture s 3 18446744073709551615 3)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 3 18446744073709551615 3) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_13_2
example (s : riscv_state) : «dfn'DIV» (2,1,0) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 3 18446744073709551615 3) else «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (0 : BitVec 64), 2) (fixture s 3 18446744073709551615 3)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 3 18446744073709551615 3) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_13_7
example (s : riscv_state) : «dfn'DIV» (7,1,0) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 3 18446744073709551615 3) else «write'GPR» (BitVec.sdiv (18446744073709551615 : BitVec 64) (0 : BitVec 64), 7) (fixture s 3 18446744073709551615 3)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 3 18446744073709551615 3) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_14_0
example (s : riscv_state) : «dfn'DIV» (0,1,1) (fixture s 3 9223372036854775808 2) = (let t := fixture s 3 9223372036854775808 2; t) := by
 change (if ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 3 9223372036854775808 2) else «write'GPR» (BitVec.sdiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 0) (fixture s 3 9223372036854775808 2)) = _
 have divisorZero : ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 0) (fixture s 3 9223372036854775808 2) = _
 have numeric : (BitVec.sdiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_14_1
example (s : riscv_state) : «dfn'DIV» (1,1,1) (fixture s 3 9223372036854775808 2) = (let t := fixture s 3 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 3 9223372036854775808 2) else «write'GPR» (BitVec.sdiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 1) (fixture s 3 9223372036854775808 2)) = _
 have divisorZero : ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 1) (fixture s 3 9223372036854775808 2) = _
 have numeric : (BitVec.sdiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_14_2
example (s : riscv_state) : «dfn'DIV» (2,1,1) (fixture s 3 9223372036854775808 2) = (let t := fixture s 3 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 3 9223372036854775808 2) else «write'GPR» (BitVec.sdiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 2) (fixture s 3 9223372036854775808 2)) = _
 have divisorZero : ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 2) (fixture s 3 9223372036854775808 2) = _
 have numeric : (BitVec.sdiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIV_3_14_7
example (s : riscv_state) : «dfn'DIV» (7,1,1) (fixture s 3 9223372036854775808 2) = (let t := fixture s 3 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 3 9223372036854775808 2) else «write'GPR» (BitVec.sdiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 7) (fixture s 3 9223372036854775808 2)) = _
 have divisorZero : ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.sdiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 7) (fixture s 3 9223372036854775808 2) = _
 have numeric : (BitVec.sdiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_0_0
example (s : riscv_state) : «dfn'REM» (0,1,2) (fixture s 0 0 0) = (let t := fixture s 0 0 0; t) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((0 : BitVec 64), 0) (fixture s 0 0 0) else «write'GPR» (BitVec.srem (0 : BitVec 64) (0 : BitVec 64), 0) (fixture s 0 0 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((0 : BitVec 64), 0) (fixture s 0 0 0) = _
 have numeric : ((0 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_0_1
example (s : riscv_state) : «dfn'REM» (1,1,2) (fixture s 0 0 0) = (let t := fixture s 0 0 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((0 : BitVec 64), 1) (fixture s 0 0 0) else «write'GPR» (BitVec.srem (0 : BitVec 64) (0 : BitVec 64), 1) (fixture s 0 0 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((0 : BitVec 64), 1) (fixture s 0 0 0) = _
 have numeric : ((0 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_0_2
example (s : riscv_state) : «dfn'REM» (2,1,2) (fixture s 0 0 0) = (let t := fixture s 0 0 0; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((0 : BitVec 64), 2) (fixture s 0 0 0) else «write'GPR» (BitVec.srem (0 : BitVec 64) (0 : BitVec 64), 2) (fixture s 0 0 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((0 : BitVec 64), 2) (fixture s 0 0 0) = _
 have numeric : ((0 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_0_7
example (s : riscv_state) : «dfn'REM» (7,1,2) (fixture s 0 0 0) = (let t := fixture s 0 0 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((0 : BitVec 64), 7) (fixture s 0 0 0) else «write'GPR» (BitVec.srem (0 : BitVec 64) (0 : BitVec 64), 7) (fixture s 0 0 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((0 : BitVec 64), 7) (fixture s 0 0 0) = _
 have numeric : ((0 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_1_0
example (s : riscv_state) : «dfn'REM» (0,1,2) (fixture s 0 17 0) = (let t := fixture s 0 17 0; t) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 0) (fixture s 0 17 0) else «write'GPR» (BitVec.srem (17 : BitVec 64) (0 : BitVec 64), 0) (fixture s 0 17 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((17 : BitVec 64), 0) (fixture s 0 17 0) = _
 have numeric : ((17 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_1_1
example (s : riscv_state) : «dfn'REM» (1,1,2) (fixture s 0 17 0) = (let t := fixture s 0 17 0; {t with c_gpr := holUpdate 7 (holUpdate 1 17 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 1) (fixture s 0 17 0) else «write'GPR» (BitVec.srem (17 : BitVec 64) (0 : BitVec 64), 1) (fixture s 0 17 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((17 : BitVec 64), 1) (fixture s 0 17 0) = _
 have numeric : ((17 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_1_2
example (s : riscv_state) : «dfn'REM» (2,1,2) (fixture s 0 17 0) = (let t := fixture s 0 17 0; {t with c_gpr := holUpdate 7 (holUpdate 2 17 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 2) (fixture s 0 17 0) else «write'GPR» (BitVec.srem (17 : BitVec 64) (0 : BitVec 64), 2) (fixture s 0 17 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((17 : BitVec 64), 2) (fixture s 0 17 0) = _
 have numeric : ((17 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_1_7
example (s : riscv_state) : «dfn'REM» (7,1,2) (fixture s 0 17 0) = (let t := fixture s 0 17 0; {t with c_gpr := holUpdate 7 (holUpdate 7 17 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 7) (fixture s 0 17 0) else «write'GPR» (BitVec.srem (17 : BitVec 64) (0 : BitVec 64), 7) (fixture s 0 17 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((17 : BitVec 64), 7) (fixture s 0 17 0) = _
 have numeric : ((17 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_2_0
example (s : riscv_state) : «dfn'REM» (0,1,2) (fixture s 0 18446744073709551615 0) = (let t := fixture s 0 18446744073709551615 0; t) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 0) (fixture s 0 18446744073709551615 0) else «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (0 : BitVec 64), 0) (fixture s 0 18446744073709551615 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((18446744073709551615 : BitVec 64), 0) (fixture s 0 18446744073709551615 0) = _
 have numeric : ((18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_2_1
example (s : riscv_state) : «dfn'REM» (1,1,2) (fixture s 0 18446744073709551615 0) = (let t := fixture s 0 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 1) (fixture s 0 18446744073709551615 0) else «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (0 : BitVec 64), 1) (fixture s 0 18446744073709551615 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((18446744073709551615 : BitVec 64), 1) (fixture s 0 18446744073709551615 0) = _
 have numeric : ((18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_2_2
example (s : riscv_state) : «dfn'REM» (2,1,2) (fixture s 0 18446744073709551615 0) = (let t := fixture s 0 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 2) (fixture s 0 18446744073709551615 0) else «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (0 : BitVec 64), 2) (fixture s 0 18446744073709551615 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((18446744073709551615 : BitVec 64), 2) (fixture s 0 18446744073709551615 0) = _
 have numeric : ((18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_2_7
example (s : riscv_state) : «dfn'REM» (7,1,2) (fixture s 0 18446744073709551615 0) = (let t := fixture s 0 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 7) (fixture s 0 18446744073709551615 0) else «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (0 : BitVec 64), 7) (fixture s 0 18446744073709551615 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((18446744073709551615 : BitVec 64), 7) (fixture s 0 18446744073709551615 0) = _
 have numeric : ((18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_3_0
example (s : riscv_state) : «dfn'REM» (0,1,2) (fixture s 0 17 3) = (let t := fixture s 0 17 3; t) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 0) (fixture s 0 17 3) else «write'GPR» (BitVec.srem (17 : BitVec 64) (3 : BitVec 64), 0) (fixture s 0 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (17 : BitVec 64) (3 : BitVec 64), 0) (fixture s 0 17 3) = _
 have numeric : (BitVec.srem (17 : BitVec 64) (3 : BitVec 64)) = (2 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_3_1
example (s : riscv_state) : «dfn'REM» (1,1,2) (fixture s 0 17 3) = (let t := fixture s 0 17 3; {t with c_gpr := holUpdate 7 (holUpdate 1 2 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 1) (fixture s 0 17 3) else «write'GPR» (BitVec.srem (17 : BitVec 64) (3 : BitVec 64), 1) (fixture s 0 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (17 : BitVec 64) (3 : BitVec 64), 1) (fixture s 0 17 3) = _
 have numeric : (BitVec.srem (17 : BitVec 64) (3 : BitVec 64)) = (2 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_3_2
example (s : riscv_state) : «dfn'REM» (2,1,2) (fixture s 0 17 3) = (let t := fixture s 0 17 3; {t with c_gpr := holUpdate 7 (holUpdate 2 2 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 2) (fixture s 0 17 3) else «write'GPR» (BitVec.srem (17 : BitVec 64) (3 : BitVec 64), 2) (fixture s 0 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (17 : BitVec 64) (3 : BitVec 64), 2) (fixture s 0 17 3) = _
 have numeric : (BitVec.srem (17 : BitVec 64) (3 : BitVec 64)) = (2 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_3_7
example (s : riscv_state) : «dfn'REM» (7,1,2) (fixture s 0 17 3) = (let t := fixture s 0 17 3; {t with c_gpr := holUpdate 7 (holUpdate 7 2 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 7) (fixture s 0 17 3) else «write'GPR» (BitVec.srem (17 : BitVec 64) (3 : BitVec 64), 7) (fixture s 0 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (17 : BitVec 64) (3 : BitVec 64), 7) (fixture s 0 17 3) = _
 have numeric : (BitVec.srem (17 : BitVec 64) (3 : BitVec 64)) = (2 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_4_0
example (s : riscv_state) : «dfn'REM» (0,1,2) (fixture s 0 18446744073709551599 3) = (let t := fixture s 0 18446744073709551599 3; t) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551599 : BitVec 64), 0) (fixture s 0 18446744073709551599 3) else «write'GPR» (BitVec.srem (18446744073709551599 : BitVec 64) (3 : BitVec 64), 0) (fixture s 0 18446744073709551599 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (18446744073709551599 : BitVec 64) (3 : BitVec 64), 0) (fixture s 0 18446744073709551599 3) = _
 have numeric : (BitVec.srem (18446744073709551599 : BitVec 64) (3 : BitVec 64)) = (18446744073709551614 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_4_1
example (s : riscv_state) : «dfn'REM» (1,1,2) (fixture s 0 18446744073709551599 3) = (let t := fixture s 0 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551599 : BitVec 64), 1) (fixture s 0 18446744073709551599 3) else «write'GPR» (BitVec.srem (18446744073709551599 : BitVec 64) (3 : BitVec 64), 1) (fixture s 0 18446744073709551599 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (18446744073709551599 : BitVec 64) (3 : BitVec 64), 1) (fixture s 0 18446744073709551599 3) = _
 have numeric : (BitVec.srem (18446744073709551599 : BitVec 64) (3 : BitVec 64)) = (18446744073709551614 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_4_2
example (s : riscv_state) : «dfn'REM» (2,1,2) (fixture s 0 18446744073709551599 3) = (let t := fixture s 0 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551599 : BitVec 64), 2) (fixture s 0 18446744073709551599 3) else «write'GPR» (BitVec.srem (18446744073709551599 : BitVec 64) (3 : BitVec 64), 2) (fixture s 0 18446744073709551599 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (18446744073709551599 : BitVec 64) (3 : BitVec 64), 2) (fixture s 0 18446744073709551599 3) = _
 have numeric : (BitVec.srem (18446744073709551599 : BitVec 64) (3 : BitVec 64)) = (18446744073709551614 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_4_7
example (s : riscv_state) : «dfn'REM» (7,1,2) (fixture s 0 18446744073709551599 3) = (let t := fixture s 0 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551599 : BitVec 64), 7) (fixture s 0 18446744073709551599 3) else «write'GPR» (BitVec.srem (18446744073709551599 : BitVec 64) (3 : BitVec 64), 7) (fixture s 0 18446744073709551599 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (18446744073709551599 : BitVec 64) (3 : BitVec 64), 7) (fixture s 0 18446744073709551599 3) = _
 have numeric : (BitVec.srem (18446744073709551599 : BitVec 64) (3 : BitVec 64)) = (18446744073709551614 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_5_0
example (s : riscv_state) : «dfn'REM» (0,1,2) (fixture s 0 17 18446744073709551613) = (let t := fixture s 0 17 18446744073709551613; t) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 0) (fixture s 0 17 18446744073709551613) else «write'GPR» (BitVec.srem (17 : BitVec 64) (18446744073709551613 : BitVec 64), 0) (fixture s 0 17 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (17 : BitVec 64) (18446744073709551613 : BitVec 64), 0) (fixture s 0 17 18446744073709551613) = _
 have numeric : (BitVec.srem (17 : BitVec 64) (18446744073709551613 : BitVec 64)) = (2 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_5_1
example (s : riscv_state) : «dfn'REM» (1,1,2) (fixture s 0 17 18446744073709551613) = (let t := fixture s 0 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 1 2 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 1) (fixture s 0 17 18446744073709551613) else «write'GPR» (BitVec.srem (17 : BitVec 64) (18446744073709551613 : BitVec 64), 1) (fixture s 0 17 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (17 : BitVec 64) (18446744073709551613 : BitVec 64), 1) (fixture s 0 17 18446744073709551613) = _
 have numeric : (BitVec.srem (17 : BitVec 64) (18446744073709551613 : BitVec 64)) = (2 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_5_2
example (s : riscv_state) : «dfn'REM» (2,1,2) (fixture s 0 17 18446744073709551613) = (let t := fixture s 0 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 2 2 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 2) (fixture s 0 17 18446744073709551613) else «write'GPR» (BitVec.srem (17 : BitVec 64) (18446744073709551613 : BitVec 64), 2) (fixture s 0 17 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (17 : BitVec 64) (18446744073709551613 : BitVec 64), 2) (fixture s 0 17 18446744073709551613) = _
 have numeric : (BitVec.srem (17 : BitVec 64) (18446744073709551613 : BitVec 64)) = (2 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_5_7
example (s : riscv_state) : «dfn'REM» (7,1,2) (fixture s 0 17 18446744073709551613) = (let t := fixture s 0 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 7 2 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 7) (fixture s 0 17 18446744073709551613) else «write'GPR» (BitVec.srem (17 : BitVec 64) (18446744073709551613 : BitVec 64), 7) (fixture s 0 17 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (17 : BitVec 64) (18446744073709551613 : BitVec 64), 7) (fixture s 0 17 18446744073709551613) = _
 have numeric : (BitVec.srem (17 : BitVec 64) (18446744073709551613 : BitVec 64)) = (2 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_6_0
example (s : riscv_state) : «dfn'REM» (0,1,2) (fixture s 0 18446744073709551599 18446744073709551613) = (let t := fixture s 0 18446744073709551599 18446744073709551613; t) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551599 : BitVec 64), 0) (fixture s 0 18446744073709551599 18446744073709551613) else «write'GPR» (BitVec.srem (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 0) (fixture s 0 18446744073709551599 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 0) (fixture s 0 18446744073709551599 18446744073709551613) = _
 have numeric : (BitVec.srem (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64)) = (18446744073709551614 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_6_1
example (s : riscv_state) : «dfn'REM» (1,1,2) (fixture s 0 18446744073709551599 18446744073709551613) = (let t := fixture s 0 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551599 : BitVec 64), 1) (fixture s 0 18446744073709551599 18446744073709551613) else «write'GPR» (BitVec.srem (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 1) (fixture s 0 18446744073709551599 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 1) (fixture s 0 18446744073709551599 18446744073709551613) = _
 have numeric : (BitVec.srem (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64)) = (18446744073709551614 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_6_2
example (s : riscv_state) : «dfn'REM» (2,1,2) (fixture s 0 18446744073709551599 18446744073709551613) = (let t := fixture s 0 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551599 : BitVec 64), 2) (fixture s 0 18446744073709551599 18446744073709551613) else «write'GPR» (BitVec.srem (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 2) (fixture s 0 18446744073709551599 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 2) (fixture s 0 18446744073709551599 18446744073709551613) = _
 have numeric : (BitVec.srem (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64)) = (18446744073709551614 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_6_7
example (s : riscv_state) : «dfn'REM» (7,1,2) (fixture s 0 18446744073709551599 18446744073709551613) = (let t := fixture s 0 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551599 : BitVec 64), 7) (fixture s 0 18446744073709551599 18446744073709551613) else «write'GPR» (BitVec.srem (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 7) (fixture s 0 18446744073709551599 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 7) (fixture s 0 18446744073709551599 18446744073709551613) = _
 have numeric : (BitVec.srem (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64)) = (18446744073709551614 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_7_0
example (s : riscv_state) : «dfn'REM» (0,1,2) (fixture s 0 9223372036854775808 18446744073709551615) = (let t := fixture s 0 9223372036854775808 18446744073709551615; t) := by
 change (if ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((9223372036854775808 : BitVec 64), 0) (fixture s 0 9223372036854775808 18446744073709551615) else «write'GPR» (BitVec.srem (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 0) (fixture s 0 9223372036854775808 18446744073709551615)) = _
 have divisorZero : ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 0) (fixture s 0 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.srem (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_7_1
example (s : riscv_state) : «dfn'REM» (1,1,2) (fixture s 0 9223372036854775808 18446744073709551615) = (let t := fixture s 0 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((9223372036854775808 : BitVec 64), 1) (fixture s 0 9223372036854775808 18446744073709551615) else «write'GPR» (BitVec.srem (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 1) (fixture s 0 9223372036854775808 18446744073709551615)) = _
 have divisorZero : ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 1) (fixture s 0 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.srem (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_7_2
example (s : riscv_state) : «dfn'REM» (2,1,2) (fixture s 0 9223372036854775808 18446744073709551615) = (let t := fixture s 0 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((9223372036854775808 : BitVec 64), 2) (fixture s 0 9223372036854775808 18446744073709551615) else «write'GPR» (BitVec.srem (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 2) (fixture s 0 9223372036854775808 18446744073709551615)) = _
 have divisorZero : ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 2) (fixture s 0 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.srem (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_7_7
example (s : riscv_state) : «dfn'REM» (7,1,2) (fixture s 0 9223372036854775808 18446744073709551615) = (let t := fixture s 0 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((9223372036854775808 : BitVec 64), 7) (fixture s 0 9223372036854775808 18446744073709551615) else «write'GPR» (BitVec.srem (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 7) (fixture s 0 9223372036854775808 18446744073709551615)) = _
 have divisorZero : ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 7) (fixture s 0 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.srem (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_8_0
example (s : riscv_state) : «dfn'REM» (0,1,2) (fixture s 0 2147483648 4294967295) = (let t := fixture s 0 2147483648 4294967295; t) := by
 change (if ((4294967295 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((2147483648 : BitVec 64), 0) (fixture s 0 2147483648 4294967295) else «write'GPR» (BitVec.srem (2147483648 : BitVec 64) (4294967295 : BitVec 64), 0) (fixture s 0 2147483648 4294967295)) = _
 have divisorZero : ((4294967295 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (2147483648 : BitVec 64) (4294967295 : BitVec 64), 0) (fixture s 0 2147483648 4294967295) = _
 have numeric : (BitVec.srem (2147483648 : BitVec 64) (4294967295 : BitVec 64)) = (2147483648 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_8_1
example (s : riscv_state) : «dfn'REM» (1,1,2) (fixture s 0 2147483648 4294967295) = (let t := fixture s 0 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 1 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967295 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((2147483648 : BitVec 64), 1) (fixture s 0 2147483648 4294967295) else «write'GPR» (BitVec.srem (2147483648 : BitVec 64) (4294967295 : BitVec 64), 1) (fixture s 0 2147483648 4294967295)) = _
 have divisorZero : ((4294967295 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (2147483648 : BitVec 64) (4294967295 : BitVec 64), 1) (fixture s 0 2147483648 4294967295) = _
 have numeric : (BitVec.srem (2147483648 : BitVec 64) (4294967295 : BitVec 64)) = (2147483648 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_8_2
example (s : riscv_state) : «dfn'REM» (2,1,2) (fixture s 0 2147483648 4294967295) = (let t := fixture s 0 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 2 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967295 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((2147483648 : BitVec 64), 2) (fixture s 0 2147483648 4294967295) else «write'GPR» (BitVec.srem (2147483648 : BitVec 64) (4294967295 : BitVec 64), 2) (fixture s 0 2147483648 4294967295)) = _
 have divisorZero : ((4294967295 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (2147483648 : BitVec 64) (4294967295 : BitVec 64), 2) (fixture s 0 2147483648 4294967295) = _
 have numeric : (BitVec.srem (2147483648 : BitVec 64) (4294967295 : BitVec 64)) = (2147483648 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_8_7
example (s : riscv_state) : «dfn'REM» (7,1,2) (fixture s 0 2147483648 4294967295) = (let t := fixture s 0 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 7 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967295 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((2147483648 : BitVec 64), 7) (fixture s 0 2147483648 4294967295) else «write'GPR» (BitVec.srem (2147483648 : BitVec 64) (4294967295 : BitVec 64), 7) (fixture s 0 2147483648 4294967295)) = _
 have divisorZero : ((4294967295 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (2147483648 : BitVec 64) (4294967295 : BitVec 64), 7) (fixture s 0 2147483648 4294967295) = _
 have numeric : (BitVec.srem (2147483648 : BitVec 64) (4294967295 : BitVec 64)) = (2147483648 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_9_0
example (s : riscv_state) : «dfn'REM» (0,1,2) (fixture s 0 4294967313 4294967296) = (let t := fixture s 0 4294967313 4294967296; t) := by
 change (if ((4294967296 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((4294967313 : BitVec 64), 0) (fixture s 0 4294967313 4294967296) else «write'GPR» (BitVec.srem (4294967313 : BitVec 64) (4294967296 : BitVec 64), 0) (fixture s 0 4294967313 4294967296)) = _
 have divisorZero : ((4294967296 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (4294967313 : BitVec 64) (4294967296 : BitVec 64), 0) (fixture s 0 4294967313 4294967296) = _
 have numeric : (BitVec.srem (4294967313 : BitVec 64) (4294967296 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_9_1
example (s : riscv_state) : «dfn'REM» (1,1,2) (fixture s 0 4294967313 4294967296) = (let t := fixture s 0 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 1 17 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967296 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((4294967313 : BitVec 64), 1) (fixture s 0 4294967313 4294967296) else «write'GPR» (BitVec.srem (4294967313 : BitVec 64) (4294967296 : BitVec 64), 1) (fixture s 0 4294967313 4294967296)) = _
 have divisorZero : ((4294967296 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (4294967313 : BitVec 64) (4294967296 : BitVec 64), 1) (fixture s 0 4294967313 4294967296) = _
 have numeric : (BitVec.srem (4294967313 : BitVec 64) (4294967296 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_9_2
example (s : riscv_state) : «dfn'REM» (2,1,2) (fixture s 0 4294967313 4294967296) = (let t := fixture s 0 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 2 17 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967296 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((4294967313 : BitVec 64), 2) (fixture s 0 4294967313 4294967296) else «write'GPR» (BitVec.srem (4294967313 : BitVec 64) (4294967296 : BitVec 64), 2) (fixture s 0 4294967313 4294967296)) = _
 have divisorZero : ((4294967296 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (4294967313 : BitVec 64) (4294967296 : BitVec 64), 2) (fixture s 0 4294967313 4294967296) = _
 have numeric : (BitVec.srem (4294967313 : BitVec 64) (4294967296 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_9_7
example (s : riscv_state) : «dfn'REM» (7,1,2) (fixture s 0 4294967313 4294967296) = (let t := fixture s 0 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 7 17 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967296 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((4294967313 : BitVec 64), 7) (fixture s 0 4294967313 4294967296) else «write'GPR» (BitVec.srem (4294967313 : BitVec 64) (4294967296 : BitVec 64), 7) (fixture s 0 4294967313 4294967296)) = _
 have divisorZero : ((4294967296 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (4294967313 : BitVec 64) (4294967296 : BitVec 64), 7) (fixture s 0 4294967313 4294967296) = _
 have numeric : (BitVec.srem (4294967313 : BitVec 64) (4294967296 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_10_0
example (s : riscv_state) : «dfn'REM» (0,1,2) (fixture s 0 18446744073709551615 2) = (let t := fixture s 0 18446744073709551615 2; t) := by
 change (if ((2 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 0) (fixture s 0 18446744073709551615 2) else «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (2 : BitVec 64), 0) (fixture s 0 18446744073709551615 2)) = _
 have divisorZero : ((2 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (2 : BitVec 64), 0) (fixture s 0 18446744073709551615 2) = _
 have numeric : (BitVec.srem (18446744073709551615 : BitVec 64) (2 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_10_1
example (s : riscv_state) : «dfn'REM» (1,1,2) (fixture s 0 18446744073709551615 2) = (let t := fixture s 0 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((2 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 1) (fixture s 0 18446744073709551615 2) else «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (2 : BitVec 64), 1) (fixture s 0 18446744073709551615 2)) = _
 have divisorZero : ((2 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (2 : BitVec 64), 1) (fixture s 0 18446744073709551615 2) = _
 have numeric : (BitVec.srem (18446744073709551615 : BitVec 64) (2 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_10_2
example (s : riscv_state) : «dfn'REM» (2,1,2) (fixture s 0 18446744073709551615 2) = (let t := fixture s 0 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((2 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 2) (fixture s 0 18446744073709551615 2) else «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (2 : BitVec 64), 2) (fixture s 0 18446744073709551615 2)) = _
 have divisorZero : ((2 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (2 : BitVec 64), 2) (fixture s 0 18446744073709551615 2) = _
 have numeric : (BitVec.srem (18446744073709551615 : BitVec 64) (2 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_10_7
example (s : riscv_state) : «dfn'REM» (7,1,2) (fixture s 0 18446744073709551615 2) = (let t := fixture s 0 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((2 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 7) (fixture s 0 18446744073709551615 2) else «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (2 : BitVec 64), 7) (fixture s 0 18446744073709551615 2)) = _
 have divisorZero : ((2 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (2 : BitVec 64), 7) (fixture s 0 18446744073709551615 2) = _
 have numeric : (BitVec.srem (18446744073709551615 : BitVec 64) (2 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_11_0
example (s : riscv_state) : «dfn'REM» (0,1,2) (fixture s 0 18446744073709551615 3) = (let t := fixture s 0 18446744073709551615 3; t) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 0) (fixture s 0 18446744073709551615 3) else «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (3 : BitVec 64), 0) (fixture s 0 18446744073709551615 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (3 : BitVec 64), 0) (fixture s 0 18446744073709551615 3) = _
 have numeric : (BitVec.srem (18446744073709551615 : BitVec 64) (3 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_11_1
example (s : riscv_state) : «dfn'REM» (1,1,2) (fixture s 0 18446744073709551615 3) = (let t := fixture s 0 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 1) (fixture s 0 18446744073709551615 3) else «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (3 : BitVec 64), 1) (fixture s 0 18446744073709551615 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (3 : BitVec 64), 1) (fixture s 0 18446744073709551615 3) = _
 have numeric : (BitVec.srem (18446744073709551615 : BitVec 64) (3 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_11_2
example (s : riscv_state) : «dfn'REM» (2,1,2) (fixture s 0 18446744073709551615 3) = (let t := fixture s 0 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 2) (fixture s 0 18446744073709551615 3) else «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (3 : BitVec 64), 2) (fixture s 0 18446744073709551615 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (3 : BitVec 64), 2) (fixture s 0 18446744073709551615 3) = _
 have numeric : (BitVec.srem (18446744073709551615 : BitVec 64) (3 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_11_7
example (s : riscv_state) : «dfn'REM» (7,1,2) (fixture s 0 18446744073709551615 3) = (let t := fixture s 0 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 7) (fixture s 0 18446744073709551615 3) else «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (3 : BitVec 64), 7) (fixture s 0 18446744073709551615 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (3 : BitVec 64), 7) (fixture s 0 18446744073709551615 3) = _
 have numeric : (BitVec.srem (18446744073709551615 : BitVec 64) (3 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_12_0
example (s : riscv_state) : «dfn'REM» (0,0,2) (fixture s 0 17 3) = (let t := fixture s 0 17 3; t) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((0 : BitVec 64), 0) (fixture s 0 17 3) else «write'GPR» (BitVec.srem (0 : BitVec 64) (3 : BitVec 64), 0) (fixture s 0 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (0 : BitVec 64) (3 : BitVec 64), 0) (fixture s 0 17 3) = _
 have numeric : (BitVec.srem (0 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_12_1
example (s : riscv_state) : «dfn'REM» (1,0,2) (fixture s 0 17 3) = (let t := fixture s 0 17 3; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((0 : BitVec 64), 1) (fixture s 0 17 3) else «write'GPR» (BitVec.srem (0 : BitVec 64) (3 : BitVec 64), 1) (fixture s 0 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (0 : BitVec 64) (3 : BitVec 64), 1) (fixture s 0 17 3) = _
 have numeric : (BitVec.srem (0 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_12_2
example (s : riscv_state) : «dfn'REM» (2,0,2) (fixture s 0 17 3) = (let t := fixture s 0 17 3; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((0 : BitVec 64), 2) (fixture s 0 17 3) else «write'GPR» (BitVec.srem (0 : BitVec 64) (3 : BitVec 64), 2) (fixture s 0 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (0 : BitVec 64) (3 : BitVec 64), 2) (fixture s 0 17 3) = _
 have numeric : (BitVec.srem (0 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_12_7
example (s : riscv_state) : «dfn'REM» (7,0,2) (fixture s 0 17 3) = (let t := fixture s 0 17 3; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((0 : BitVec 64), 7) (fixture s 0 17 3) else «write'GPR» (BitVec.srem (0 : BitVec 64) (3 : BitVec 64), 7) (fixture s 0 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (0 : BitVec 64) (3 : BitVec 64), 7) (fixture s 0 17 3) = _
 have numeric : (BitVec.srem (0 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_13_0
example (s : riscv_state) : «dfn'REM» (0,1,0) (fixture s 0 18446744073709551615 3) = (let t := fixture s 0 18446744073709551615 3; t) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 0) (fixture s 0 18446744073709551615 3) else «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (0 : BitVec 64), 0) (fixture s 0 18446744073709551615 3)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((18446744073709551615 : BitVec 64), 0) (fixture s 0 18446744073709551615 3) = _
 have numeric : ((18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_13_1
example (s : riscv_state) : «dfn'REM» (1,1,0) (fixture s 0 18446744073709551615 3) = (let t := fixture s 0 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 1) (fixture s 0 18446744073709551615 3) else «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (0 : BitVec 64), 1) (fixture s 0 18446744073709551615 3)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((18446744073709551615 : BitVec 64), 1) (fixture s 0 18446744073709551615 3) = _
 have numeric : ((18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_13_2
example (s : riscv_state) : «dfn'REM» (2,1,0) (fixture s 0 18446744073709551615 3) = (let t := fixture s 0 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 2) (fixture s 0 18446744073709551615 3) else «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (0 : BitVec 64), 2) (fixture s 0 18446744073709551615 3)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((18446744073709551615 : BitVec 64), 2) (fixture s 0 18446744073709551615 3) = _
 have numeric : ((18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_13_7
example (s : riscv_state) : «dfn'REM» (7,1,0) (fixture s 0 18446744073709551615 3) = (let t := fixture s 0 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 7) (fixture s 0 18446744073709551615 3) else «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (0 : BitVec 64), 7) (fixture s 0 18446744073709551615 3)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((18446744073709551615 : BitVec 64), 7) (fixture s 0 18446744073709551615 3) = _
 have numeric : ((18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_14_0
example (s : riscv_state) : «dfn'REM» (0,1,1) (fixture s 0 9223372036854775808 2) = (let t := fixture s 0 9223372036854775808 2; t) := by
 change (if ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((9223372036854775808 : BitVec 64), 0) (fixture s 0 9223372036854775808 2) else «write'GPR» (BitVec.srem (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 0) (fixture s 0 9223372036854775808 2)) = _
 have divisorZero : ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 0) (fixture s 0 9223372036854775808 2) = _
 have numeric : (BitVec.srem (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_14_1
example (s : riscv_state) : «dfn'REM» (1,1,1) (fixture s 0 9223372036854775808 2) = (let t := fixture s 0 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((9223372036854775808 : BitVec 64), 1) (fixture s 0 9223372036854775808 2) else «write'GPR» (BitVec.srem (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 1) (fixture s 0 9223372036854775808 2)) = _
 have divisorZero : ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 1) (fixture s 0 9223372036854775808 2) = _
 have numeric : (BitVec.srem (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_14_2
example (s : riscv_state) : «dfn'REM» (2,1,1) (fixture s 0 9223372036854775808 2) = (let t := fixture s 0 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((9223372036854775808 : BitVec 64), 2) (fixture s 0 9223372036854775808 2) else «write'GPR» (BitVec.srem (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 2) (fixture s 0 9223372036854775808 2)) = _
 have divisorZero : ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 2) (fixture s 0 9223372036854775808 2) = _
 have numeric : (BitVec.srem (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_0_14_7
example (s : riscv_state) : «dfn'REM» (7,1,1) (fixture s 0 9223372036854775808 2) = (let t := fixture s 0 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((9223372036854775808 : BitVec 64), 7) (fixture s 0 9223372036854775808 2) else «write'GPR» (BitVec.srem (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 7) (fixture s 0 9223372036854775808 2)) = _
 have divisorZero : ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 7) (fixture s 0 9223372036854775808 2) = _
 have numeric : (BitVec.srem (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_0_0
example (s : riscv_state) : «dfn'REM» (0,1,2) (fixture s 2 0 0) = (let t := fixture s 2 0 0; t) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((0 : BitVec 64), 0) (fixture s 2 0 0) else «write'GPR» (BitVec.srem (0 : BitVec 64) (0 : BitVec 64), 0) (fixture s 2 0 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((0 : BitVec 64), 0) (fixture s 2 0 0) = _
 have numeric : ((0 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_0_1
example (s : riscv_state) : «dfn'REM» (1,1,2) (fixture s 2 0 0) = (let t := fixture s 2 0 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((0 : BitVec 64), 1) (fixture s 2 0 0) else «write'GPR» (BitVec.srem (0 : BitVec 64) (0 : BitVec 64), 1) (fixture s 2 0 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((0 : BitVec 64), 1) (fixture s 2 0 0) = _
 have numeric : ((0 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_0_2
example (s : riscv_state) : «dfn'REM» (2,1,2) (fixture s 2 0 0) = (let t := fixture s 2 0 0; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((0 : BitVec 64), 2) (fixture s 2 0 0) else «write'GPR» (BitVec.srem (0 : BitVec 64) (0 : BitVec 64), 2) (fixture s 2 0 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((0 : BitVec 64), 2) (fixture s 2 0 0) = _
 have numeric : ((0 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_0_7
example (s : riscv_state) : «dfn'REM» (7,1,2) (fixture s 2 0 0) = (let t := fixture s 2 0 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((0 : BitVec 64), 7) (fixture s 2 0 0) else «write'GPR» (BitVec.srem (0 : BitVec 64) (0 : BitVec 64), 7) (fixture s 2 0 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((0 : BitVec 64), 7) (fixture s 2 0 0) = _
 have numeric : ((0 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_1_0
example (s : riscv_state) : «dfn'REM» (0,1,2) (fixture s 2 17 0) = (let t := fixture s 2 17 0; t) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 0) (fixture s 2 17 0) else «write'GPR» (BitVec.srem (17 : BitVec 64) (0 : BitVec 64), 0) (fixture s 2 17 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((17 : BitVec 64), 0) (fixture s 2 17 0) = _
 have numeric : ((17 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_1_1
example (s : riscv_state) : «dfn'REM» (1,1,2) (fixture s 2 17 0) = (let t := fixture s 2 17 0; {t with c_gpr := holUpdate 7 (holUpdate 1 17 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 1) (fixture s 2 17 0) else «write'GPR» (BitVec.srem (17 : BitVec 64) (0 : BitVec 64), 1) (fixture s 2 17 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((17 : BitVec 64), 1) (fixture s 2 17 0) = _
 have numeric : ((17 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_1_2
example (s : riscv_state) : «dfn'REM» (2,1,2) (fixture s 2 17 0) = (let t := fixture s 2 17 0; {t with c_gpr := holUpdate 7 (holUpdate 2 17 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 2) (fixture s 2 17 0) else «write'GPR» (BitVec.srem (17 : BitVec 64) (0 : BitVec 64), 2) (fixture s 2 17 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((17 : BitVec 64), 2) (fixture s 2 17 0) = _
 have numeric : ((17 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_1_7
example (s : riscv_state) : «dfn'REM» (7,1,2) (fixture s 2 17 0) = (let t := fixture s 2 17 0; {t with c_gpr := holUpdate 7 (holUpdate 7 17 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 7) (fixture s 2 17 0) else «write'GPR» (BitVec.srem (17 : BitVec 64) (0 : BitVec 64), 7) (fixture s 2 17 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((17 : BitVec 64), 7) (fixture s 2 17 0) = _
 have numeric : ((17 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_2_0
example (s : riscv_state) : «dfn'REM» (0,1,2) (fixture s 2 18446744073709551615 0) = (let t := fixture s 2 18446744073709551615 0; t) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 0) (fixture s 2 18446744073709551615 0) else «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (0 : BitVec 64), 0) (fixture s 2 18446744073709551615 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((18446744073709551615 : BitVec 64), 0) (fixture s 2 18446744073709551615 0) = _
 have numeric : ((18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_2_1
example (s : riscv_state) : «dfn'REM» (1,1,2) (fixture s 2 18446744073709551615 0) = (let t := fixture s 2 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 1) (fixture s 2 18446744073709551615 0) else «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (0 : BitVec 64), 1) (fixture s 2 18446744073709551615 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((18446744073709551615 : BitVec 64), 1) (fixture s 2 18446744073709551615 0) = _
 have numeric : ((18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_2_2
example (s : riscv_state) : «dfn'REM» (2,1,2) (fixture s 2 18446744073709551615 0) = (let t := fixture s 2 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 2) (fixture s 2 18446744073709551615 0) else «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (0 : BitVec 64), 2) (fixture s 2 18446744073709551615 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((18446744073709551615 : BitVec 64), 2) (fixture s 2 18446744073709551615 0) = _
 have numeric : ((18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_2_7
example (s : riscv_state) : «dfn'REM» (7,1,2) (fixture s 2 18446744073709551615 0) = (let t := fixture s 2 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 7) (fixture s 2 18446744073709551615 0) else «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (0 : BitVec 64), 7) (fixture s 2 18446744073709551615 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((18446744073709551615 : BitVec 64), 7) (fixture s 2 18446744073709551615 0) = _
 have numeric : ((18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_3_0
example (s : riscv_state) : «dfn'REM» (0,1,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; t) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 0) (fixture s 2 17 3) else «write'GPR» (BitVec.srem (17 : BitVec 64) (3 : BitVec 64), 0) (fixture s 2 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (17 : BitVec 64) (3 : BitVec 64), 0) (fixture s 2 17 3) = _
 have numeric : (BitVec.srem (17 : BitVec 64) (3 : BitVec 64)) = (2 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_3_1
example (s : riscv_state) : «dfn'REM» (1,1,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; {t with c_gpr := holUpdate 7 (holUpdate 1 2 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 1) (fixture s 2 17 3) else «write'GPR» (BitVec.srem (17 : BitVec 64) (3 : BitVec 64), 1) (fixture s 2 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (17 : BitVec 64) (3 : BitVec 64), 1) (fixture s 2 17 3) = _
 have numeric : (BitVec.srem (17 : BitVec 64) (3 : BitVec 64)) = (2 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_3_2
example (s : riscv_state) : «dfn'REM» (2,1,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; {t with c_gpr := holUpdate 7 (holUpdate 2 2 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 2) (fixture s 2 17 3) else «write'GPR» (BitVec.srem (17 : BitVec 64) (3 : BitVec 64), 2) (fixture s 2 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (17 : BitVec 64) (3 : BitVec 64), 2) (fixture s 2 17 3) = _
 have numeric : (BitVec.srem (17 : BitVec 64) (3 : BitVec 64)) = (2 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_3_7
example (s : riscv_state) : «dfn'REM» (7,1,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; {t with c_gpr := holUpdate 7 (holUpdate 7 2 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 7) (fixture s 2 17 3) else «write'GPR» (BitVec.srem (17 : BitVec 64) (3 : BitVec 64), 7) (fixture s 2 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (17 : BitVec 64) (3 : BitVec 64), 7) (fixture s 2 17 3) = _
 have numeric : (BitVec.srem (17 : BitVec 64) (3 : BitVec 64)) = (2 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_4_0
example (s : riscv_state) : «dfn'REM» (0,1,2) (fixture s 2 18446744073709551599 3) = (let t := fixture s 2 18446744073709551599 3; t) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551599 : BitVec 64), 0) (fixture s 2 18446744073709551599 3) else «write'GPR» (BitVec.srem (18446744073709551599 : BitVec 64) (3 : BitVec 64), 0) (fixture s 2 18446744073709551599 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (18446744073709551599 : BitVec 64) (3 : BitVec 64), 0) (fixture s 2 18446744073709551599 3) = _
 have numeric : (BitVec.srem (18446744073709551599 : BitVec 64) (3 : BitVec 64)) = (18446744073709551614 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_4_1
example (s : riscv_state) : «dfn'REM» (1,1,2) (fixture s 2 18446744073709551599 3) = (let t := fixture s 2 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551599 : BitVec 64), 1) (fixture s 2 18446744073709551599 3) else «write'GPR» (BitVec.srem (18446744073709551599 : BitVec 64) (3 : BitVec 64), 1) (fixture s 2 18446744073709551599 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (18446744073709551599 : BitVec 64) (3 : BitVec 64), 1) (fixture s 2 18446744073709551599 3) = _
 have numeric : (BitVec.srem (18446744073709551599 : BitVec 64) (3 : BitVec 64)) = (18446744073709551614 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_4_2
example (s : riscv_state) : «dfn'REM» (2,1,2) (fixture s 2 18446744073709551599 3) = (let t := fixture s 2 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551599 : BitVec 64), 2) (fixture s 2 18446744073709551599 3) else «write'GPR» (BitVec.srem (18446744073709551599 : BitVec 64) (3 : BitVec 64), 2) (fixture s 2 18446744073709551599 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (18446744073709551599 : BitVec 64) (3 : BitVec 64), 2) (fixture s 2 18446744073709551599 3) = _
 have numeric : (BitVec.srem (18446744073709551599 : BitVec 64) (3 : BitVec 64)) = (18446744073709551614 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_4_7
example (s : riscv_state) : «dfn'REM» (7,1,2) (fixture s 2 18446744073709551599 3) = (let t := fixture s 2 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551599 : BitVec 64), 7) (fixture s 2 18446744073709551599 3) else «write'GPR» (BitVec.srem (18446744073709551599 : BitVec 64) (3 : BitVec 64), 7) (fixture s 2 18446744073709551599 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (18446744073709551599 : BitVec 64) (3 : BitVec 64), 7) (fixture s 2 18446744073709551599 3) = _
 have numeric : (BitVec.srem (18446744073709551599 : BitVec 64) (3 : BitVec 64)) = (18446744073709551614 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_5_0
example (s : riscv_state) : «dfn'REM» (0,1,2) (fixture s 2 17 18446744073709551613) = (let t := fixture s 2 17 18446744073709551613; t) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 0) (fixture s 2 17 18446744073709551613) else «write'GPR» (BitVec.srem (17 : BitVec 64) (18446744073709551613 : BitVec 64), 0) (fixture s 2 17 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (17 : BitVec 64) (18446744073709551613 : BitVec 64), 0) (fixture s 2 17 18446744073709551613) = _
 have numeric : (BitVec.srem (17 : BitVec 64) (18446744073709551613 : BitVec 64)) = (2 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_5_1
example (s : riscv_state) : «dfn'REM» (1,1,2) (fixture s 2 17 18446744073709551613) = (let t := fixture s 2 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 1 2 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 1) (fixture s 2 17 18446744073709551613) else «write'GPR» (BitVec.srem (17 : BitVec 64) (18446744073709551613 : BitVec 64), 1) (fixture s 2 17 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (17 : BitVec 64) (18446744073709551613 : BitVec 64), 1) (fixture s 2 17 18446744073709551613) = _
 have numeric : (BitVec.srem (17 : BitVec 64) (18446744073709551613 : BitVec 64)) = (2 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_5_2
example (s : riscv_state) : «dfn'REM» (2,1,2) (fixture s 2 17 18446744073709551613) = (let t := fixture s 2 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 2 2 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 2) (fixture s 2 17 18446744073709551613) else «write'GPR» (BitVec.srem (17 : BitVec 64) (18446744073709551613 : BitVec 64), 2) (fixture s 2 17 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (17 : BitVec 64) (18446744073709551613 : BitVec 64), 2) (fixture s 2 17 18446744073709551613) = _
 have numeric : (BitVec.srem (17 : BitVec 64) (18446744073709551613 : BitVec 64)) = (2 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_5_7
example (s : riscv_state) : «dfn'REM» (7,1,2) (fixture s 2 17 18446744073709551613) = (let t := fixture s 2 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 7 2 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 7) (fixture s 2 17 18446744073709551613) else «write'GPR» (BitVec.srem (17 : BitVec 64) (18446744073709551613 : BitVec 64), 7) (fixture s 2 17 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (17 : BitVec 64) (18446744073709551613 : BitVec 64), 7) (fixture s 2 17 18446744073709551613) = _
 have numeric : (BitVec.srem (17 : BitVec 64) (18446744073709551613 : BitVec 64)) = (2 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_6_0
example (s : riscv_state) : «dfn'REM» (0,1,2) (fixture s 2 18446744073709551599 18446744073709551613) = (let t := fixture s 2 18446744073709551599 18446744073709551613; t) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551599 : BitVec 64), 0) (fixture s 2 18446744073709551599 18446744073709551613) else «write'GPR» (BitVec.srem (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 0) (fixture s 2 18446744073709551599 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 0) (fixture s 2 18446744073709551599 18446744073709551613) = _
 have numeric : (BitVec.srem (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64)) = (18446744073709551614 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_6_1
example (s : riscv_state) : «dfn'REM» (1,1,2) (fixture s 2 18446744073709551599 18446744073709551613) = (let t := fixture s 2 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551599 : BitVec 64), 1) (fixture s 2 18446744073709551599 18446744073709551613) else «write'GPR» (BitVec.srem (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 1) (fixture s 2 18446744073709551599 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 1) (fixture s 2 18446744073709551599 18446744073709551613) = _
 have numeric : (BitVec.srem (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64)) = (18446744073709551614 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_6_2
example (s : riscv_state) : «dfn'REM» (2,1,2) (fixture s 2 18446744073709551599 18446744073709551613) = (let t := fixture s 2 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551599 : BitVec 64), 2) (fixture s 2 18446744073709551599 18446744073709551613) else «write'GPR» (BitVec.srem (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 2) (fixture s 2 18446744073709551599 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 2) (fixture s 2 18446744073709551599 18446744073709551613) = _
 have numeric : (BitVec.srem (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64)) = (18446744073709551614 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_6_7
example (s : riscv_state) : «dfn'REM» (7,1,2) (fixture s 2 18446744073709551599 18446744073709551613) = (let t := fixture s 2 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551599 : BitVec 64), 7) (fixture s 2 18446744073709551599 18446744073709551613) else «write'GPR» (BitVec.srem (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 7) (fixture s 2 18446744073709551599 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 7) (fixture s 2 18446744073709551599 18446744073709551613) = _
 have numeric : (BitVec.srem (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64)) = (18446744073709551614 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_7_0
example (s : riscv_state) : «dfn'REM» (0,1,2) (fixture s 2 9223372036854775808 18446744073709551615) = (let t := fixture s 2 9223372036854775808 18446744073709551615; t) := by
 change (if ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((9223372036854775808 : BitVec 64), 0) (fixture s 2 9223372036854775808 18446744073709551615) else «write'GPR» (BitVec.srem (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 0) (fixture s 2 9223372036854775808 18446744073709551615)) = _
 have divisorZero : ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 0) (fixture s 2 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.srem (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_7_1
example (s : riscv_state) : «dfn'REM» (1,1,2) (fixture s 2 9223372036854775808 18446744073709551615) = (let t := fixture s 2 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((9223372036854775808 : BitVec 64), 1) (fixture s 2 9223372036854775808 18446744073709551615) else «write'GPR» (BitVec.srem (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 1) (fixture s 2 9223372036854775808 18446744073709551615)) = _
 have divisorZero : ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 1) (fixture s 2 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.srem (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_7_2
example (s : riscv_state) : «dfn'REM» (2,1,2) (fixture s 2 9223372036854775808 18446744073709551615) = (let t := fixture s 2 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((9223372036854775808 : BitVec 64), 2) (fixture s 2 9223372036854775808 18446744073709551615) else «write'GPR» (BitVec.srem (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 2) (fixture s 2 9223372036854775808 18446744073709551615)) = _
 have divisorZero : ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 2) (fixture s 2 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.srem (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_7_7
example (s : riscv_state) : «dfn'REM» (7,1,2) (fixture s 2 9223372036854775808 18446744073709551615) = (let t := fixture s 2 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((9223372036854775808 : BitVec 64), 7) (fixture s 2 9223372036854775808 18446744073709551615) else «write'GPR» (BitVec.srem (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 7) (fixture s 2 9223372036854775808 18446744073709551615)) = _
 have divisorZero : ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 7) (fixture s 2 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.srem (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_8_0
example (s : riscv_state) : «dfn'REM» (0,1,2) (fixture s 2 2147483648 4294967295) = (let t := fixture s 2 2147483648 4294967295; t) := by
 change (if ((4294967295 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((2147483648 : BitVec 64), 0) (fixture s 2 2147483648 4294967295) else «write'GPR» (BitVec.srem (2147483648 : BitVec 64) (4294967295 : BitVec 64), 0) (fixture s 2 2147483648 4294967295)) = _
 have divisorZero : ((4294967295 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (2147483648 : BitVec 64) (4294967295 : BitVec 64), 0) (fixture s 2 2147483648 4294967295) = _
 have numeric : (BitVec.srem (2147483648 : BitVec 64) (4294967295 : BitVec 64)) = (2147483648 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_8_1
example (s : riscv_state) : «dfn'REM» (1,1,2) (fixture s 2 2147483648 4294967295) = (let t := fixture s 2 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 1 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967295 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((2147483648 : BitVec 64), 1) (fixture s 2 2147483648 4294967295) else «write'GPR» (BitVec.srem (2147483648 : BitVec 64) (4294967295 : BitVec 64), 1) (fixture s 2 2147483648 4294967295)) = _
 have divisorZero : ((4294967295 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (2147483648 : BitVec 64) (4294967295 : BitVec 64), 1) (fixture s 2 2147483648 4294967295) = _
 have numeric : (BitVec.srem (2147483648 : BitVec 64) (4294967295 : BitVec 64)) = (2147483648 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_8_2
example (s : riscv_state) : «dfn'REM» (2,1,2) (fixture s 2 2147483648 4294967295) = (let t := fixture s 2 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 2 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967295 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((2147483648 : BitVec 64), 2) (fixture s 2 2147483648 4294967295) else «write'GPR» (BitVec.srem (2147483648 : BitVec 64) (4294967295 : BitVec 64), 2) (fixture s 2 2147483648 4294967295)) = _
 have divisorZero : ((4294967295 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (2147483648 : BitVec 64) (4294967295 : BitVec 64), 2) (fixture s 2 2147483648 4294967295) = _
 have numeric : (BitVec.srem (2147483648 : BitVec 64) (4294967295 : BitVec 64)) = (2147483648 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_8_7
example (s : riscv_state) : «dfn'REM» (7,1,2) (fixture s 2 2147483648 4294967295) = (let t := fixture s 2 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 7 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967295 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((2147483648 : BitVec 64), 7) (fixture s 2 2147483648 4294967295) else «write'GPR» (BitVec.srem (2147483648 : BitVec 64) (4294967295 : BitVec 64), 7) (fixture s 2 2147483648 4294967295)) = _
 have divisorZero : ((4294967295 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (2147483648 : BitVec 64) (4294967295 : BitVec 64), 7) (fixture s 2 2147483648 4294967295) = _
 have numeric : (BitVec.srem (2147483648 : BitVec 64) (4294967295 : BitVec 64)) = (2147483648 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_9_0
example (s : riscv_state) : «dfn'REM» (0,1,2) (fixture s 2 4294967313 4294967296) = (let t := fixture s 2 4294967313 4294967296; t) := by
 change (if ((4294967296 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((4294967313 : BitVec 64), 0) (fixture s 2 4294967313 4294967296) else «write'GPR» (BitVec.srem (4294967313 : BitVec 64) (4294967296 : BitVec 64), 0) (fixture s 2 4294967313 4294967296)) = _
 have divisorZero : ((4294967296 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (4294967313 : BitVec 64) (4294967296 : BitVec 64), 0) (fixture s 2 4294967313 4294967296) = _
 have numeric : (BitVec.srem (4294967313 : BitVec 64) (4294967296 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_9_1
example (s : riscv_state) : «dfn'REM» (1,1,2) (fixture s 2 4294967313 4294967296) = (let t := fixture s 2 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 1 17 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967296 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((4294967313 : BitVec 64), 1) (fixture s 2 4294967313 4294967296) else «write'GPR» (BitVec.srem (4294967313 : BitVec 64) (4294967296 : BitVec 64), 1) (fixture s 2 4294967313 4294967296)) = _
 have divisorZero : ((4294967296 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (4294967313 : BitVec 64) (4294967296 : BitVec 64), 1) (fixture s 2 4294967313 4294967296) = _
 have numeric : (BitVec.srem (4294967313 : BitVec 64) (4294967296 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_9_2
example (s : riscv_state) : «dfn'REM» (2,1,2) (fixture s 2 4294967313 4294967296) = (let t := fixture s 2 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 2 17 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967296 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((4294967313 : BitVec 64), 2) (fixture s 2 4294967313 4294967296) else «write'GPR» (BitVec.srem (4294967313 : BitVec 64) (4294967296 : BitVec 64), 2) (fixture s 2 4294967313 4294967296)) = _
 have divisorZero : ((4294967296 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (4294967313 : BitVec 64) (4294967296 : BitVec 64), 2) (fixture s 2 4294967313 4294967296) = _
 have numeric : (BitVec.srem (4294967313 : BitVec 64) (4294967296 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_9_7
example (s : riscv_state) : «dfn'REM» (7,1,2) (fixture s 2 4294967313 4294967296) = (let t := fixture s 2 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 7 17 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967296 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((4294967313 : BitVec 64), 7) (fixture s 2 4294967313 4294967296) else «write'GPR» (BitVec.srem (4294967313 : BitVec 64) (4294967296 : BitVec 64), 7) (fixture s 2 4294967313 4294967296)) = _
 have divisorZero : ((4294967296 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (4294967313 : BitVec 64) (4294967296 : BitVec 64), 7) (fixture s 2 4294967313 4294967296) = _
 have numeric : (BitVec.srem (4294967313 : BitVec 64) (4294967296 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_10_0
example (s : riscv_state) : «dfn'REM» (0,1,2) (fixture s 2 18446744073709551615 2) = (let t := fixture s 2 18446744073709551615 2; t) := by
 change (if ((2 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 0) (fixture s 2 18446744073709551615 2) else «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (2 : BitVec 64), 0) (fixture s 2 18446744073709551615 2)) = _
 have divisorZero : ((2 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (2 : BitVec 64), 0) (fixture s 2 18446744073709551615 2) = _
 have numeric : (BitVec.srem (18446744073709551615 : BitVec 64) (2 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_10_1
example (s : riscv_state) : «dfn'REM» (1,1,2) (fixture s 2 18446744073709551615 2) = (let t := fixture s 2 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((2 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 1) (fixture s 2 18446744073709551615 2) else «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (2 : BitVec 64), 1) (fixture s 2 18446744073709551615 2)) = _
 have divisorZero : ((2 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (2 : BitVec 64), 1) (fixture s 2 18446744073709551615 2) = _
 have numeric : (BitVec.srem (18446744073709551615 : BitVec 64) (2 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_10_2
example (s : riscv_state) : «dfn'REM» (2,1,2) (fixture s 2 18446744073709551615 2) = (let t := fixture s 2 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((2 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 2) (fixture s 2 18446744073709551615 2) else «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (2 : BitVec 64), 2) (fixture s 2 18446744073709551615 2)) = _
 have divisorZero : ((2 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (2 : BitVec 64), 2) (fixture s 2 18446744073709551615 2) = _
 have numeric : (BitVec.srem (18446744073709551615 : BitVec 64) (2 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_10_7
example (s : riscv_state) : «dfn'REM» (7,1,2) (fixture s 2 18446744073709551615 2) = (let t := fixture s 2 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((2 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 7) (fixture s 2 18446744073709551615 2) else «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (2 : BitVec 64), 7) (fixture s 2 18446744073709551615 2)) = _
 have divisorZero : ((2 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (2 : BitVec 64), 7) (fixture s 2 18446744073709551615 2) = _
 have numeric : (BitVec.srem (18446744073709551615 : BitVec 64) (2 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_11_0
example (s : riscv_state) : «dfn'REM» (0,1,2) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; t) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 0) (fixture s 2 18446744073709551615 3) else «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (3 : BitVec 64), 0) (fixture s 2 18446744073709551615 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (3 : BitVec 64), 0) (fixture s 2 18446744073709551615 3) = _
 have numeric : (BitVec.srem (18446744073709551615 : BitVec 64) (3 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_11_1
example (s : riscv_state) : «dfn'REM» (1,1,2) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 1) (fixture s 2 18446744073709551615 3) else «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (3 : BitVec 64), 1) (fixture s 2 18446744073709551615 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (3 : BitVec 64), 1) (fixture s 2 18446744073709551615 3) = _
 have numeric : (BitVec.srem (18446744073709551615 : BitVec 64) (3 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_11_2
example (s : riscv_state) : «dfn'REM» (2,1,2) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 2) (fixture s 2 18446744073709551615 3) else «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (3 : BitVec 64), 2) (fixture s 2 18446744073709551615 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (3 : BitVec 64), 2) (fixture s 2 18446744073709551615 3) = _
 have numeric : (BitVec.srem (18446744073709551615 : BitVec 64) (3 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_11_7
example (s : riscv_state) : «dfn'REM» (7,1,2) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 7) (fixture s 2 18446744073709551615 3) else «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (3 : BitVec 64), 7) (fixture s 2 18446744073709551615 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (3 : BitVec 64), 7) (fixture s 2 18446744073709551615 3) = _
 have numeric : (BitVec.srem (18446744073709551615 : BitVec 64) (3 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_12_0
example (s : riscv_state) : «dfn'REM» (0,0,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; t) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((0 : BitVec 64), 0) (fixture s 2 17 3) else «write'GPR» (BitVec.srem (0 : BitVec 64) (3 : BitVec 64), 0) (fixture s 2 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (0 : BitVec 64) (3 : BitVec 64), 0) (fixture s 2 17 3) = _
 have numeric : (BitVec.srem (0 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_12_1
example (s : riscv_state) : «dfn'REM» (1,0,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((0 : BitVec 64), 1) (fixture s 2 17 3) else «write'GPR» (BitVec.srem (0 : BitVec 64) (3 : BitVec 64), 1) (fixture s 2 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (0 : BitVec 64) (3 : BitVec 64), 1) (fixture s 2 17 3) = _
 have numeric : (BitVec.srem (0 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_12_2
example (s : riscv_state) : «dfn'REM» (2,0,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((0 : BitVec 64), 2) (fixture s 2 17 3) else «write'GPR» (BitVec.srem (0 : BitVec 64) (3 : BitVec 64), 2) (fixture s 2 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (0 : BitVec 64) (3 : BitVec 64), 2) (fixture s 2 17 3) = _
 have numeric : (BitVec.srem (0 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_12_7
example (s : riscv_state) : «dfn'REM» (7,0,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((0 : BitVec 64), 7) (fixture s 2 17 3) else «write'GPR» (BitVec.srem (0 : BitVec 64) (3 : BitVec 64), 7) (fixture s 2 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (0 : BitVec 64) (3 : BitVec 64), 7) (fixture s 2 17 3) = _
 have numeric : (BitVec.srem (0 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_13_0
example (s : riscv_state) : «dfn'REM» (0,1,0) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; t) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 0) (fixture s 2 18446744073709551615 3) else «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (0 : BitVec 64), 0) (fixture s 2 18446744073709551615 3)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((18446744073709551615 : BitVec 64), 0) (fixture s 2 18446744073709551615 3) = _
 have numeric : ((18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_13_1
example (s : riscv_state) : «dfn'REM» (1,1,0) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 1) (fixture s 2 18446744073709551615 3) else «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (0 : BitVec 64), 1) (fixture s 2 18446744073709551615 3)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((18446744073709551615 : BitVec 64), 1) (fixture s 2 18446744073709551615 3) = _
 have numeric : ((18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_13_2
example (s : riscv_state) : «dfn'REM» (2,1,0) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 2) (fixture s 2 18446744073709551615 3) else «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (0 : BitVec 64), 2) (fixture s 2 18446744073709551615 3)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((18446744073709551615 : BitVec 64), 2) (fixture s 2 18446744073709551615 3) = _
 have numeric : ((18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_13_7
example (s : riscv_state) : «dfn'REM» (7,1,0) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 7) (fixture s 2 18446744073709551615 3) else «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (0 : BitVec 64), 7) (fixture s 2 18446744073709551615 3)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((18446744073709551615 : BitVec 64), 7) (fixture s 2 18446744073709551615 3) = _
 have numeric : ((18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_14_0
example (s : riscv_state) : «dfn'REM» (0,1,1) (fixture s 2 9223372036854775808 2) = (let t := fixture s 2 9223372036854775808 2; t) := by
 change (if ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((9223372036854775808 : BitVec 64), 0) (fixture s 2 9223372036854775808 2) else «write'GPR» (BitVec.srem (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 0) (fixture s 2 9223372036854775808 2)) = _
 have divisorZero : ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 0) (fixture s 2 9223372036854775808 2) = _
 have numeric : (BitVec.srem (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_14_1
example (s : riscv_state) : «dfn'REM» (1,1,1) (fixture s 2 9223372036854775808 2) = (let t := fixture s 2 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((9223372036854775808 : BitVec 64), 1) (fixture s 2 9223372036854775808 2) else «write'GPR» (BitVec.srem (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 1) (fixture s 2 9223372036854775808 2)) = _
 have divisorZero : ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 1) (fixture s 2 9223372036854775808 2) = _
 have numeric : (BitVec.srem (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_14_2
example (s : riscv_state) : «dfn'REM» (2,1,1) (fixture s 2 9223372036854775808 2) = (let t := fixture s 2 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((9223372036854775808 : BitVec 64), 2) (fixture s 2 9223372036854775808 2) else «write'GPR» (BitVec.srem (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 2) (fixture s 2 9223372036854775808 2)) = _
 have divisorZero : ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 2) (fixture s 2 9223372036854775808 2) = _
 have numeric : (BitVec.srem (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_2_14_7
example (s : riscv_state) : «dfn'REM» (7,1,1) (fixture s 2 9223372036854775808 2) = (let t := fixture s 2 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((9223372036854775808 : BitVec 64), 7) (fixture s 2 9223372036854775808 2) else «write'GPR» (BitVec.srem (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 7) (fixture s 2 9223372036854775808 2)) = _
 have divisorZero : ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 7) (fixture s 2 9223372036854775808 2) = _
 have numeric : (BitVec.srem (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_0_0
example (s : riscv_state) : «dfn'REM» (0,1,2) (fixture s 3 0 0) = (let t := fixture s 3 0 0; t) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((0 : BitVec 64), 0) (fixture s 3 0 0) else «write'GPR» (BitVec.srem (0 : BitVec 64) (0 : BitVec 64), 0) (fixture s 3 0 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((0 : BitVec 64), 0) (fixture s 3 0 0) = _
 have numeric : ((0 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_0_1
example (s : riscv_state) : «dfn'REM» (1,1,2) (fixture s 3 0 0) = (let t := fixture s 3 0 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((0 : BitVec 64), 1) (fixture s 3 0 0) else «write'GPR» (BitVec.srem (0 : BitVec 64) (0 : BitVec 64), 1) (fixture s 3 0 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((0 : BitVec 64), 1) (fixture s 3 0 0) = _
 have numeric : ((0 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_0_2
example (s : riscv_state) : «dfn'REM» (2,1,2) (fixture s 3 0 0) = (let t := fixture s 3 0 0; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((0 : BitVec 64), 2) (fixture s 3 0 0) else «write'GPR» (BitVec.srem (0 : BitVec 64) (0 : BitVec 64), 2) (fixture s 3 0 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((0 : BitVec 64), 2) (fixture s 3 0 0) = _
 have numeric : ((0 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_0_7
example (s : riscv_state) : «dfn'REM» (7,1,2) (fixture s 3 0 0) = (let t := fixture s 3 0 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((0 : BitVec 64), 7) (fixture s 3 0 0) else «write'GPR» (BitVec.srem (0 : BitVec 64) (0 : BitVec 64), 7) (fixture s 3 0 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((0 : BitVec 64), 7) (fixture s 3 0 0) = _
 have numeric : ((0 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_1_0
example (s : riscv_state) : «dfn'REM» (0,1,2) (fixture s 3 17 0) = (let t := fixture s 3 17 0; t) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 0) (fixture s 3 17 0) else «write'GPR» (BitVec.srem (17 : BitVec 64) (0 : BitVec 64), 0) (fixture s 3 17 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((17 : BitVec 64), 0) (fixture s 3 17 0) = _
 have numeric : ((17 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_1_1
example (s : riscv_state) : «dfn'REM» (1,1,2) (fixture s 3 17 0) = (let t := fixture s 3 17 0; {t with c_gpr := holUpdate 7 (holUpdate 1 17 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 1) (fixture s 3 17 0) else «write'GPR» (BitVec.srem (17 : BitVec 64) (0 : BitVec 64), 1) (fixture s 3 17 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((17 : BitVec 64), 1) (fixture s 3 17 0) = _
 have numeric : ((17 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_1_2
example (s : riscv_state) : «dfn'REM» (2,1,2) (fixture s 3 17 0) = (let t := fixture s 3 17 0; {t with c_gpr := holUpdate 7 (holUpdate 2 17 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 2) (fixture s 3 17 0) else «write'GPR» (BitVec.srem (17 : BitVec 64) (0 : BitVec 64), 2) (fixture s 3 17 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((17 : BitVec 64), 2) (fixture s 3 17 0) = _
 have numeric : ((17 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_1_7
example (s : riscv_state) : «dfn'REM» (7,1,2) (fixture s 3 17 0) = (let t := fixture s 3 17 0; {t with c_gpr := holUpdate 7 (holUpdate 7 17 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 7) (fixture s 3 17 0) else «write'GPR» (BitVec.srem (17 : BitVec 64) (0 : BitVec 64), 7) (fixture s 3 17 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((17 : BitVec 64), 7) (fixture s 3 17 0) = _
 have numeric : ((17 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_2_0
example (s : riscv_state) : «dfn'REM» (0,1,2) (fixture s 3 18446744073709551615 0) = (let t := fixture s 3 18446744073709551615 0; t) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 0) (fixture s 3 18446744073709551615 0) else «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (0 : BitVec 64), 0) (fixture s 3 18446744073709551615 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((18446744073709551615 : BitVec 64), 0) (fixture s 3 18446744073709551615 0) = _
 have numeric : ((18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_2_1
example (s : riscv_state) : «dfn'REM» (1,1,2) (fixture s 3 18446744073709551615 0) = (let t := fixture s 3 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 1) (fixture s 3 18446744073709551615 0) else «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (0 : BitVec 64), 1) (fixture s 3 18446744073709551615 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((18446744073709551615 : BitVec 64), 1) (fixture s 3 18446744073709551615 0) = _
 have numeric : ((18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_2_2
example (s : riscv_state) : «dfn'REM» (2,1,2) (fixture s 3 18446744073709551615 0) = (let t := fixture s 3 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 2) (fixture s 3 18446744073709551615 0) else «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (0 : BitVec 64), 2) (fixture s 3 18446744073709551615 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((18446744073709551615 : BitVec 64), 2) (fixture s 3 18446744073709551615 0) = _
 have numeric : ((18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_2_7
example (s : riscv_state) : «dfn'REM» (7,1,2) (fixture s 3 18446744073709551615 0) = (let t := fixture s 3 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 7) (fixture s 3 18446744073709551615 0) else «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (0 : BitVec 64), 7) (fixture s 3 18446744073709551615 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((18446744073709551615 : BitVec 64), 7) (fixture s 3 18446744073709551615 0) = _
 have numeric : ((18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_3_0
example (s : riscv_state) : «dfn'REM» (0,1,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; t) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 0) (fixture s 3 17 3) else «write'GPR» (BitVec.srem (17 : BitVec 64) (3 : BitVec 64), 0) (fixture s 3 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (17 : BitVec 64) (3 : BitVec 64), 0) (fixture s 3 17 3) = _
 have numeric : (BitVec.srem (17 : BitVec 64) (3 : BitVec 64)) = (2 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_3_1
example (s : riscv_state) : «dfn'REM» (1,1,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; {t with c_gpr := holUpdate 7 (holUpdate 1 2 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 1) (fixture s 3 17 3) else «write'GPR» (BitVec.srem (17 : BitVec 64) (3 : BitVec 64), 1) (fixture s 3 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (17 : BitVec 64) (3 : BitVec 64), 1) (fixture s 3 17 3) = _
 have numeric : (BitVec.srem (17 : BitVec 64) (3 : BitVec 64)) = (2 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_3_2
example (s : riscv_state) : «dfn'REM» (2,1,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; {t with c_gpr := holUpdate 7 (holUpdate 2 2 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 2) (fixture s 3 17 3) else «write'GPR» (BitVec.srem (17 : BitVec 64) (3 : BitVec 64), 2) (fixture s 3 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (17 : BitVec 64) (3 : BitVec 64), 2) (fixture s 3 17 3) = _
 have numeric : (BitVec.srem (17 : BitVec 64) (3 : BitVec 64)) = (2 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_3_7
example (s : riscv_state) : «dfn'REM» (7,1,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; {t with c_gpr := holUpdate 7 (holUpdate 7 2 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 7) (fixture s 3 17 3) else «write'GPR» (BitVec.srem (17 : BitVec 64) (3 : BitVec 64), 7) (fixture s 3 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (17 : BitVec 64) (3 : BitVec 64), 7) (fixture s 3 17 3) = _
 have numeric : (BitVec.srem (17 : BitVec 64) (3 : BitVec 64)) = (2 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_4_0
example (s : riscv_state) : «dfn'REM» (0,1,2) (fixture s 3 18446744073709551599 3) = (let t := fixture s 3 18446744073709551599 3; t) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551599 : BitVec 64), 0) (fixture s 3 18446744073709551599 3) else «write'GPR» (BitVec.srem (18446744073709551599 : BitVec 64) (3 : BitVec 64), 0) (fixture s 3 18446744073709551599 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (18446744073709551599 : BitVec 64) (3 : BitVec 64), 0) (fixture s 3 18446744073709551599 3) = _
 have numeric : (BitVec.srem (18446744073709551599 : BitVec 64) (3 : BitVec 64)) = (18446744073709551614 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_4_1
example (s : riscv_state) : «dfn'REM» (1,1,2) (fixture s 3 18446744073709551599 3) = (let t := fixture s 3 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551599 : BitVec 64), 1) (fixture s 3 18446744073709551599 3) else «write'GPR» (BitVec.srem (18446744073709551599 : BitVec 64) (3 : BitVec 64), 1) (fixture s 3 18446744073709551599 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (18446744073709551599 : BitVec 64) (3 : BitVec 64), 1) (fixture s 3 18446744073709551599 3) = _
 have numeric : (BitVec.srem (18446744073709551599 : BitVec 64) (3 : BitVec 64)) = (18446744073709551614 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_4_2
example (s : riscv_state) : «dfn'REM» (2,1,2) (fixture s 3 18446744073709551599 3) = (let t := fixture s 3 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551599 : BitVec 64), 2) (fixture s 3 18446744073709551599 3) else «write'GPR» (BitVec.srem (18446744073709551599 : BitVec 64) (3 : BitVec 64), 2) (fixture s 3 18446744073709551599 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (18446744073709551599 : BitVec 64) (3 : BitVec 64), 2) (fixture s 3 18446744073709551599 3) = _
 have numeric : (BitVec.srem (18446744073709551599 : BitVec 64) (3 : BitVec 64)) = (18446744073709551614 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_4_7
example (s : riscv_state) : «dfn'REM» (7,1,2) (fixture s 3 18446744073709551599 3) = (let t := fixture s 3 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551599 : BitVec 64), 7) (fixture s 3 18446744073709551599 3) else «write'GPR» (BitVec.srem (18446744073709551599 : BitVec 64) (3 : BitVec 64), 7) (fixture s 3 18446744073709551599 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (18446744073709551599 : BitVec 64) (3 : BitVec 64), 7) (fixture s 3 18446744073709551599 3) = _
 have numeric : (BitVec.srem (18446744073709551599 : BitVec 64) (3 : BitVec 64)) = (18446744073709551614 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_5_0
example (s : riscv_state) : «dfn'REM» (0,1,2) (fixture s 3 17 18446744073709551613) = (let t := fixture s 3 17 18446744073709551613; t) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 0) (fixture s 3 17 18446744073709551613) else «write'GPR» (BitVec.srem (17 : BitVec 64) (18446744073709551613 : BitVec 64), 0) (fixture s 3 17 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (17 : BitVec 64) (18446744073709551613 : BitVec 64), 0) (fixture s 3 17 18446744073709551613) = _
 have numeric : (BitVec.srem (17 : BitVec 64) (18446744073709551613 : BitVec 64)) = (2 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_5_1
example (s : riscv_state) : «dfn'REM» (1,1,2) (fixture s 3 17 18446744073709551613) = (let t := fixture s 3 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 1 2 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 1) (fixture s 3 17 18446744073709551613) else «write'GPR» (BitVec.srem (17 : BitVec 64) (18446744073709551613 : BitVec 64), 1) (fixture s 3 17 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (17 : BitVec 64) (18446744073709551613 : BitVec 64), 1) (fixture s 3 17 18446744073709551613) = _
 have numeric : (BitVec.srem (17 : BitVec 64) (18446744073709551613 : BitVec 64)) = (2 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_5_2
example (s : riscv_state) : «dfn'REM» (2,1,2) (fixture s 3 17 18446744073709551613) = (let t := fixture s 3 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 2 2 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 2) (fixture s 3 17 18446744073709551613) else «write'GPR» (BitVec.srem (17 : BitVec 64) (18446744073709551613 : BitVec 64), 2) (fixture s 3 17 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (17 : BitVec 64) (18446744073709551613 : BitVec 64), 2) (fixture s 3 17 18446744073709551613) = _
 have numeric : (BitVec.srem (17 : BitVec 64) (18446744073709551613 : BitVec 64)) = (2 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_5_7
example (s : riscv_state) : «dfn'REM» (7,1,2) (fixture s 3 17 18446744073709551613) = (let t := fixture s 3 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 7 2 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 7) (fixture s 3 17 18446744073709551613) else «write'GPR» (BitVec.srem (17 : BitVec 64) (18446744073709551613 : BitVec 64), 7) (fixture s 3 17 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (17 : BitVec 64) (18446744073709551613 : BitVec 64), 7) (fixture s 3 17 18446744073709551613) = _
 have numeric : (BitVec.srem (17 : BitVec 64) (18446744073709551613 : BitVec 64)) = (2 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_6_0
example (s : riscv_state) : «dfn'REM» (0,1,2) (fixture s 3 18446744073709551599 18446744073709551613) = (let t := fixture s 3 18446744073709551599 18446744073709551613; t) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551599 : BitVec 64), 0) (fixture s 3 18446744073709551599 18446744073709551613) else «write'GPR» (BitVec.srem (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 0) (fixture s 3 18446744073709551599 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 0) (fixture s 3 18446744073709551599 18446744073709551613) = _
 have numeric : (BitVec.srem (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64)) = (18446744073709551614 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_6_1
example (s : riscv_state) : «dfn'REM» (1,1,2) (fixture s 3 18446744073709551599 18446744073709551613) = (let t := fixture s 3 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551599 : BitVec 64), 1) (fixture s 3 18446744073709551599 18446744073709551613) else «write'GPR» (BitVec.srem (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 1) (fixture s 3 18446744073709551599 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 1) (fixture s 3 18446744073709551599 18446744073709551613) = _
 have numeric : (BitVec.srem (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64)) = (18446744073709551614 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_6_2
example (s : riscv_state) : «dfn'REM» (2,1,2) (fixture s 3 18446744073709551599 18446744073709551613) = (let t := fixture s 3 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551599 : BitVec 64), 2) (fixture s 3 18446744073709551599 18446744073709551613) else «write'GPR» (BitVec.srem (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 2) (fixture s 3 18446744073709551599 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 2) (fixture s 3 18446744073709551599 18446744073709551613) = _
 have numeric : (BitVec.srem (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64)) = (18446744073709551614 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_6_7
example (s : riscv_state) : «dfn'REM» (7,1,2) (fixture s 3 18446744073709551599 18446744073709551613) = (let t := fixture s 3 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551599 : BitVec 64), 7) (fixture s 3 18446744073709551599 18446744073709551613) else «write'GPR» (BitVec.srem (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 7) (fixture s 3 18446744073709551599 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 7) (fixture s 3 18446744073709551599 18446744073709551613) = _
 have numeric : (BitVec.srem (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64)) = (18446744073709551614 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_7_0
example (s : riscv_state) : «dfn'REM» (0,1,2) (fixture s 3 9223372036854775808 18446744073709551615) = (let t := fixture s 3 9223372036854775808 18446744073709551615; t) := by
 change (if ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((9223372036854775808 : BitVec 64), 0) (fixture s 3 9223372036854775808 18446744073709551615) else «write'GPR» (BitVec.srem (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 0) (fixture s 3 9223372036854775808 18446744073709551615)) = _
 have divisorZero : ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 0) (fixture s 3 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.srem (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_7_1
example (s : riscv_state) : «dfn'REM» (1,1,2) (fixture s 3 9223372036854775808 18446744073709551615) = (let t := fixture s 3 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((9223372036854775808 : BitVec 64), 1) (fixture s 3 9223372036854775808 18446744073709551615) else «write'GPR» (BitVec.srem (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 1) (fixture s 3 9223372036854775808 18446744073709551615)) = _
 have divisorZero : ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 1) (fixture s 3 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.srem (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_7_2
example (s : riscv_state) : «dfn'REM» (2,1,2) (fixture s 3 9223372036854775808 18446744073709551615) = (let t := fixture s 3 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((9223372036854775808 : BitVec 64), 2) (fixture s 3 9223372036854775808 18446744073709551615) else «write'GPR» (BitVec.srem (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 2) (fixture s 3 9223372036854775808 18446744073709551615)) = _
 have divisorZero : ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 2) (fixture s 3 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.srem (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_7_7
example (s : riscv_state) : «dfn'REM» (7,1,2) (fixture s 3 9223372036854775808 18446744073709551615) = (let t := fixture s 3 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((9223372036854775808 : BitVec 64), 7) (fixture s 3 9223372036854775808 18446744073709551615) else «write'GPR» (BitVec.srem (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 7) (fixture s 3 9223372036854775808 18446744073709551615)) = _
 have divisorZero : ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 7) (fixture s 3 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.srem (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_8_0
example (s : riscv_state) : «dfn'REM» (0,1,2) (fixture s 3 2147483648 4294967295) = (let t := fixture s 3 2147483648 4294967295; t) := by
 change (if ((4294967295 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((2147483648 : BitVec 64), 0) (fixture s 3 2147483648 4294967295) else «write'GPR» (BitVec.srem (2147483648 : BitVec 64) (4294967295 : BitVec 64), 0) (fixture s 3 2147483648 4294967295)) = _
 have divisorZero : ((4294967295 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (2147483648 : BitVec 64) (4294967295 : BitVec 64), 0) (fixture s 3 2147483648 4294967295) = _
 have numeric : (BitVec.srem (2147483648 : BitVec 64) (4294967295 : BitVec 64)) = (2147483648 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_8_1
example (s : riscv_state) : «dfn'REM» (1,1,2) (fixture s 3 2147483648 4294967295) = (let t := fixture s 3 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 1 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967295 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((2147483648 : BitVec 64), 1) (fixture s 3 2147483648 4294967295) else «write'GPR» (BitVec.srem (2147483648 : BitVec 64) (4294967295 : BitVec 64), 1) (fixture s 3 2147483648 4294967295)) = _
 have divisorZero : ((4294967295 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (2147483648 : BitVec 64) (4294967295 : BitVec 64), 1) (fixture s 3 2147483648 4294967295) = _
 have numeric : (BitVec.srem (2147483648 : BitVec 64) (4294967295 : BitVec 64)) = (2147483648 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_8_2
example (s : riscv_state) : «dfn'REM» (2,1,2) (fixture s 3 2147483648 4294967295) = (let t := fixture s 3 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 2 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967295 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((2147483648 : BitVec 64), 2) (fixture s 3 2147483648 4294967295) else «write'GPR» (BitVec.srem (2147483648 : BitVec 64) (4294967295 : BitVec 64), 2) (fixture s 3 2147483648 4294967295)) = _
 have divisorZero : ((4294967295 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (2147483648 : BitVec 64) (4294967295 : BitVec 64), 2) (fixture s 3 2147483648 4294967295) = _
 have numeric : (BitVec.srem (2147483648 : BitVec 64) (4294967295 : BitVec 64)) = (2147483648 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_8_7
example (s : riscv_state) : «dfn'REM» (7,1,2) (fixture s 3 2147483648 4294967295) = (let t := fixture s 3 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 7 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967295 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((2147483648 : BitVec 64), 7) (fixture s 3 2147483648 4294967295) else «write'GPR» (BitVec.srem (2147483648 : BitVec 64) (4294967295 : BitVec 64), 7) (fixture s 3 2147483648 4294967295)) = _
 have divisorZero : ((4294967295 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (2147483648 : BitVec 64) (4294967295 : BitVec 64), 7) (fixture s 3 2147483648 4294967295) = _
 have numeric : (BitVec.srem (2147483648 : BitVec 64) (4294967295 : BitVec 64)) = (2147483648 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_9_0
example (s : riscv_state) : «dfn'REM» (0,1,2) (fixture s 3 4294967313 4294967296) = (let t := fixture s 3 4294967313 4294967296; t) := by
 change (if ((4294967296 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((4294967313 : BitVec 64), 0) (fixture s 3 4294967313 4294967296) else «write'GPR» (BitVec.srem (4294967313 : BitVec 64) (4294967296 : BitVec 64), 0) (fixture s 3 4294967313 4294967296)) = _
 have divisorZero : ((4294967296 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (4294967313 : BitVec 64) (4294967296 : BitVec 64), 0) (fixture s 3 4294967313 4294967296) = _
 have numeric : (BitVec.srem (4294967313 : BitVec 64) (4294967296 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_9_1
example (s : riscv_state) : «dfn'REM» (1,1,2) (fixture s 3 4294967313 4294967296) = (let t := fixture s 3 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 1 17 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967296 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((4294967313 : BitVec 64), 1) (fixture s 3 4294967313 4294967296) else «write'GPR» (BitVec.srem (4294967313 : BitVec 64) (4294967296 : BitVec 64), 1) (fixture s 3 4294967313 4294967296)) = _
 have divisorZero : ((4294967296 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (4294967313 : BitVec 64) (4294967296 : BitVec 64), 1) (fixture s 3 4294967313 4294967296) = _
 have numeric : (BitVec.srem (4294967313 : BitVec 64) (4294967296 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_9_2
example (s : riscv_state) : «dfn'REM» (2,1,2) (fixture s 3 4294967313 4294967296) = (let t := fixture s 3 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 2 17 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967296 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((4294967313 : BitVec 64), 2) (fixture s 3 4294967313 4294967296) else «write'GPR» (BitVec.srem (4294967313 : BitVec 64) (4294967296 : BitVec 64), 2) (fixture s 3 4294967313 4294967296)) = _
 have divisorZero : ((4294967296 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (4294967313 : BitVec 64) (4294967296 : BitVec 64), 2) (fixture s 3 4294967313 4294967296) = _
 have numeric : (BitVec.srem (4294967313 : BitVec 64) (4294967296 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_9_7
example (s : riscv_state) : «dfn'REM» (7,1,2) (fixture s 3 4294967313 4294967296) = (let t := fixture s 3 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 7 17 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967296 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((4294967313 : BitVec 64), 7) (fixture s 3 4294967313 4294967296) else «write'GPR» (BitVec.srem (4294967313 : BitVec 64) (4294967296 : BitVec 64), 7) (fixture s 3 4294967313 4294967296)) = _
 have divisorZero : ((4294967296 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (4294967313 : BitVec 64) (4294967296 : BitVec 64), 7) (fixture s 3 4294967313 4294967296) = _
 have numeric : (BitVec.srem (4294967313 : BitVec 64) (4294967296 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_10_0
example (s : riscv_state) : «dfn'REM» (0,1,2) (fixture s 3 18446744073709551615 2) = (let t := fixture s 3 18446744073709551615 2; t) := by
 change (if ((2 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 0) (fixture s 3 18446744073709551615 2) else «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (2 : BitVec 64), 0) (fixture s 3 18446744073709551615 2)) = _
 have divisorZero : ((2 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (2 : BitVec 64), 0) (fixture s 3 18446744073709551615 2) = _
 have numeric : (BitVec.srem (18446744073709551615 : BitVec 64) (2 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_10_1
example (s : riscv_state) : «dfn'REM» (1,1,2) (fixture s 3 18446744073709551615 2) = (let t := fixture s 3 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((2 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 1) (fixture s 3 18446744073709551615 2) else «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (2 : BitVec 64), 1) (fixture s 3 18446744073709551615 2)) = _
 have divisorZero : ((2 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (2 : BitVec 64), 1) (fixture s 3 18446744073709551615 2) = _
 have numeric : (BitVec.srem (18446744073709551615 : BitVec 64) (2 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_10_2
example (s : riscv_state) : «dfn'REM» (2,1,2) (fixture s 3 18446744073709551615 2) = (let t := fixture s 3 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((2 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 2) (fixture s 3 18446744073709551615 2) else «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (2 : BitVec 64), 2) (fixture s 3 18446744073709551615 2)) = _
 have divisorZero : ((2 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (2 : BitVec 64), 2) (fixture s 3 18446744073709551615 2) = _
 have numeric : (BitVec.srem (18446744073709551615 : BitVec 64) (2 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_10_7
example (s : riscv_state) : «dfn'REM» (7,1,2) (fixture s 3 18446744073709551615 2) = (let t := fixture s 3 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((2 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 7) (fixture s 3 18446744073709551615 2) else «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (2 : BitVec 64), 7) (fixture s 3 18446744073709551615 2)) = _
 have divisorZero : ((2 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (2 : BitVec 64), 7) (fixture s 3 18446744073709551615 2) = _
 have numeric : (BitVec.srem (18446744073709551615 : BitVec 64) (2 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_11_0
example (s : riscv_state) : «dfn'REM» (0,1,2) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; t) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 0) (fixture s 3 18446744073709551615 3) else «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (3 : BitVec 64), 0) (fixture s 3 18446744073709551615 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (3 : BitVec 64), 0) (fixture s 3 18446744073709551615 3) = _
 have numeric : (BitVec.srem (18446744073709551615 : BitVec 64) (3 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_11_1
example (s : riscv_state) : «dfn'REM» (1,1,2) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 1) (fixture s 3 18446744073709551615 3) else «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (3 : BitVec 64), 1) (fixture s 3 18446744073709551615 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (3 : BitVec 64), 1) (fixture s 3 18446744073709551615 3) = _
 have numeric : (BitVec.srem (18446744073709551615 : BitVec 64) (3 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_11_2
example (s : riscv_state) : «dfn'REM» (2,1,2) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 2) (fixture s 3 18446744073709551615 3) else «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (3 : BitVec 64), 2) (fixture s 3 18446744073709551615 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (3 : BitVec 64), 2) (fixture s 3 18446744073709551615 3) = _
 have numeric : (BitVec.srem (18446744073709551615 : BitVec 64) (3 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_11_7
example (s : riscv_state) : «dfn'REM» (7,1,2) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 7) (fixture s 3 18446744073709551615 3) else «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (3 : BitVec 64), 7) (fixture s 3 18446744073709551615 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (3 : BitVec 64), 7) (fixture s 3 18446744073709551615 3) = _
 have numeric : (BitVec.srem (18446744073709551615 : BitVec 64) (3 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_12_0
example (s : riscv_state) : «dfn'REM» (0,0,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; t) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((0 : BitVec 64), 0) (fixture s 3 17 3) else «write'GPR» (BitVec.srem (0 : BitVec 64) (3 : BitVec 64), 0) (fixture s 3 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (0 : BitVec 64) (3 : BitVec 64), 0) (fixture s 3 17 3) = _
 have numeric : (BitVec.srem (0 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_12_1
example (s : riscv_state) : «dfn'REM» (1,0,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((0 : BitVec 64), 1) (fixture s 3 17 3) else «write'GPR» (BitVec.srem (0 : BitVec 64) (3 : BitVec 64), 1) (fixture s 3 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (0 : BitVec 64) (3 : BitVec 64), 1) (fixture s 3 17 3) = _
 have numeric : (BitVec.srem (0 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_12_2
example (s : riscv_state) : «dfn'REM» (2,0,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((0 : BitVec 64), 2) (fixture s 3 17 3) else «write'GPR» (BitVec.srem (0 : BitVec 64) (3 : BitVec 64), 2) (fixture s 3 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (0 : BitVec 64) (3 : BitVec 64), 2) (fixture s 3 17 3) = _
 have numeric : (BitVec.srem (0 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_12_7
example (s : riscv_state) : «dfn'REM» (7,0,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((0 : BitVec 64), 7) (fixture s 3 17 3) else «write'GPR» (BitVec.srem (0 : BitVec 64) (3 : BitVec 64), 7) (fixture s 3 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (0 : BitVec 64) (3 : BitVec 64), 7) (fixture s 3 17 3) = _
 have numeric : (BitVec.srem (0 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_13_0
example (s : riscv_state) : «dfn'REM» (0,1,0) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; t) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 0) (fixture s 3 18446744073709551615 3) else «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (0 : BitVec 64), 0) (fixture s 3 18446744073709551615 3)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((18446744073709551615 : BitVec 64), 0) (fixture s 3 18446744073709551615 3) = _
 have numeric : ((18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_13_1
example (s : riscv_state) : «dfn'REM» (1,1,0) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 1) (fixture s 3 18446744073709551615 3) else «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (0 : BitVec 64), 1) (fixture s 3 18446744073709551615 3)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((18446744073709551615 : BitVec 64), 1) (fixture s 3 18446744073709551615 3) = _
 have numeric : ((18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_13_2
example (s : riscv_state) : «dfn'REM» (2,1,0) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 2) (fixture s 3 18446744073709551615 3) else «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (0 : BitVec 64), 2) (fixture s 3 18446744073709551615 3)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((18446744073709551615 : BitVec 64), 2) (fixture s 3 18446744073709551615 3) = _
 have numeric : ((18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_13_7
example (s : riscv_state) : «dfn'REM» (7,1,0) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 7) (fixture s 3 18446744073709551615 3) else «write'GPR» (BitVec.srem (18446744073709551615 : BitVec 64) (0 : BitVec 64), 7) (fixture s 3 18446744073709551615 3)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((18446744073709551615 : BitVec 64), 7) (fixture s 3 18446744073709551615 3) = _
 have numeric : ((18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_14_0
example (s : riscv_state) : «dfn'REM» (0,1,1) (fixture s 3 9223372036854775808 2) = (let t := fixture s 3 9223372036854775808 2; t) := by
 change (if ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((9223372036854775808 : BitVec 64), 0) (fixture s 3 9223372036854775808 2) else «write'GPR» (BitVec.srem (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 0) (fixture s 3 9223372036854775808 2)) = _
 have divisorZero : ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 0) (fixture s 3 9223372036854775808 2) = _
 have numeric : (BitVec.srem (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_14_1
example (s : riscv_state) : «dfn'REM» (1,1,1) (fixture s 3 9223372036854775808 2) = (let t := fixture s 3 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((9223372036854775808 : BitVec 64), 1) (fixture s 3 9223372036854775808 2) else «write'GPR» (BitVec.srem (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 1) (fixture s 3 9223372036854775808 2)) = _
 have divisorZero : ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 1) (fixture s 3 9223372036854775808 2) = _
 have numeric : (BitVec.srem (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_14_2
example (s : riscv_state) : «dfn'REM» (2,1,1) (fixture s 3 9223372036854775808 2) = (let t := fixture s 3 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((9223372036854775808 : BitVec 64), 2) (fixture s 3 9223372036854775808 2) else «write'GPR» (BitVec.srem (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 2) (fixture s 3 9223372036854775808 2)) = _
 have divisorZero : ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 2) (fixture s 3 9223372036854775808 2) = _
 have numeric : (BitVec.srem (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REM_3_14_7
example (s : riscv_state) : «dfn'REM» (7,1,1) (fixture s 3 9223372036854775808 2) = (let t := fixture s 3 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((9223372036854775808 : BitVec 64), 7) (fixture s 3 9223372036854775808 2) else «write'GPR» (BitVec.srem (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 7) (fixture s 3 9223372036854775808 2)) = _
 have divisorZero : ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.srem (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 7) (fixture s 3 9223372036854775808 2) = _
 have numeric : (BitVec.srem (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_0_0
example (s : riscv_state) : «dfn'DIVU» (0,1,2) (fixture s 0 0 0) = (let t := fixture s 0 0 0; t) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 0 0 0) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))), 0) (fixture s 0 0 0)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 0 0 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_0_1
example (s : riscv_state) : «dfn'DIVU» (1,1,2) (fixture s 0 0 0) = (let t := fixture s 0 0 0; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 0 0 0) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))), 1) (fixture s 0 0 0)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 0 0 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_0_2
example (s : riscv_state) : «dfn'DIVU» (2,1,2) (fixture s 0 0 0) = (let t := fixture s 0 0 0; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 0 0 0) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))), 2) (fixture s 0 0 0)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 0 0 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_0_7
example (s : riscv_state) : «dfn'DIVU» (7,1,2) (fixture s 0 0 0) = (let t := fixture s 0 0 0; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 0 0 0) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))), 7) (fixture s 0 0 0)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 0 0 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_1_0
example (s : riscv_state) : «dfn'DIVU» (0,1,2) (fixture s 0 17 0) = (let t := fixture s 0 17 0; t) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 0 17 0) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (17 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))), 0) (fixture s 0 17 0)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 0 17 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_1_1
example (s : riscv_state) : «dfn'DIVU» (1,1,2) (fixture s 0 17 0) = (let t := fixture s 0 17 0; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 0 17 0) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (17 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))), 1) (fixture s 0 17 0)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 0 17 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_1_2
example (s : riscv_state) : «dfn'DIVU» (2,1,2) (fixture s 0 17 0) = (let t := fixture s 0 17 0; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 0 17 0) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (17 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))), 2) (fixture s 0 17 0)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 0 17 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_1_7
example (s : riscv_state) : «dfn'DIVU» (7,1,2) (fixture s 0 17 0) = (let t := fixture s 0 17 0; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 0 17 0) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (17 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))), 7) (fixture s 0 17 0)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 0 17 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_2_0
example (s : riscv_state) : «dfn'DIVU» (0,1,2) (fixture s 0 18446744073709551615 0) = (let t := fixture s 0 18446744073709551615 0; t) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 0 18446744073709551615 0) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))), 0) (fixture s 0 18446744073709551615 0)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 0 18446744073709551615 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_2_1
example (s : riscv_state) : «dfn'DIVU» (1,1,2) (fixture s 0 18446744073709551615 0) = (let t := fixture s 0 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 0 18446744073709551615 0) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))), 1) (fixture s 0 18446744073709551615 0)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 0 18446744073709551615 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_2_2
example (s : riscv_state) : «dfn'DIVU» (2,1,2) (fixture s 0 18446744073709551615 0) = (let t := fixture s 0 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 0 18446744073709551615 0) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))), 2) (fixture s 0 18446744073709551615 0)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 0 18446744073709551615 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_2_7
example (s : riscv_state) : «dfn'DIVU» (7,1,2) (fixture s 0 18446744073709551615 0) = (let t := fixture s 0 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 0 18446744073709551615 0) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))), 7) (fixture s 0 18446744073709551615 0)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 0 18446744073709551615 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_3_0
example (s : riscv_state) : «dfn'DIVU» (0,1,2) (fixture s 0 17 3) = (let t := fixture s 0 17 3; t) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 0 17 3) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (17 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))), 0) (fixture s 0 17 3)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (17 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))), 0) (fixture s 0 17 3) = _
 have numeric : (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (17 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64)))) = (5 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_3_1
example (s : riscv_state) : «dfn'DIVU» (1,1,2) (fixture s 0 17 3) = (let t := fixture s 0 17 3; {t with c_gpr := holUpdate 7 (holUpdate 1 5 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 0 17 3) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (17 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))), 1) (fixture s 0 17 3)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (17 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))), 1) (fixture s 0 17 3) = _
 have numeric : (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (17 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64)))) = (5 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_3_2
example (s : riscv_state) : «dfn'DIVU» (2,1,2) (fixture s 0 17 3) = (let t := fixture s 0 17 3; {t with c_gpr := holUpdate 7 (holUpdate 2 5 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 0 17 3) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (17 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))), 2) (fixture s 0 17 3)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (17 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))), 2) (fixture s 0 17 3) = _
 have numeric : (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (17 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64)))) = (5 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_3_7
example (s : riscv_state) : «dfn'DIVU» (7,1,2) (fixture s 0 17 3) = (let t := fixture s 0 17 3; {t with c_gpr := holUpdate 7 (holUpdate 7 5 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 0 17 3) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (17 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))), 7) (fixture s 0 17 3)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (17 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))), 7) (fixture s 0 17 3) = _
 have numeric : (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (17 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64)))) = (5 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_4_0
example (s : riscv_state) : «dfn'DIVU» (0,1,2) (fixture s 0 18446744073709551599 3) = (let t := fixture s 0 18446744073709551599 3; t) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 0 18446744073709551599 3) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551599 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))), 0) (fixture s 0 18446744073709551599 3)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551599 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))), 0) (fixture s 0 18446744073709551599 3) = _
 have numeric : (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551599 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64)))) = (1431655759 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_4_1
example (s : riscv_state) : «dfn'DIVU» (1,1,2) (fixture s 0 18446744073709551599 3) = (let t := fixture s 0 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 1 1431655759 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 0 18446744073709551599 3) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551599 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))), 1) (fixture s 0 18446744073709551599 3)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551599 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))), 1) (fixture s 0 18446744073709551599 3) = _
 have numeric : (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551599 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64)))) = (1431655759 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_4_2
example (s : riscv_state) : «dfn'DIVU» (2,1,2) (fixture s 0 18446744073709551599 3) = (let t := fixture s 0 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 2 1431655759 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 0 18446744073709551599 3) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551599 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))), 2) (fixture s 0 18446744073709551599 3)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551599 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))), 2) (fixture s 0 18446744073709551599 3) = _
 have numeric : (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551599 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64)))) = (1431655759 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_4_7
example (s : riscv_state) : «dfn'DIVU» (7,1,2) (fixture s 0 18446744073709551599 3) = (let t := fixture s 0 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 7 1431655759 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 0 18446744073709551599 3) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551599 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))), 7) (fixture s 0 18446744073709551599 3)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551599 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))), 7) (fixture s 0 18446744073709551599 3) = _
 have numeric : (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551599 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64)))) = (1431655759 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_5_0
example (s : riscv_state) : «dfn'DIVU» (0,1,2) (fixture s 0 17 18446744073709551613) = (let t := fixture s 0 17 18446744073709551613; t) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551613 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 0 17 18446744073709551613) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (17 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551613 : BitVec 64))), 0) (fixture s 0 17 18446744073709551613)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551613 : BitVec 64))) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (17 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551613 : BitVec 64))), 0) (fixture s 0 17 18446744073709551613) = _
 have numeric : (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (17 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551613 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_5_1
example (s : riscv_state) : «dfn'DIVU» (1,1,2) (fixture s 0 17 18446744073709551613) = (let t := fixture s 0 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551613 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 0 17 18446744073709551613) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (17 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551613 : BitVec 64))), 1) (fixture s 0 17 18446744073709551613)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551613 : BitVec 64))) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (17 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551613 : BitVec 64))), 1) (fixture s 0 17 18446744073709551613) = _
 have numeric : (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (17 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551613 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_5_2
example (s : riscv_state) : «dfn'DIVU» (2,1,2) (fixture s 0 17 18446744073709551613) = (let t := fixture s 0 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551613 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 0 17 18446744073709551613) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (17 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551613 : BitVec 64))), 2) (fixture s 0 17 18446744073709551613)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551613 : BitVec 64))) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (17 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551613 : BitVec 64))), 2) (fixture s 0 17 18446744073709551613) = _
 have numeric : (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (17 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551613 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_5_7
example (s : riscv_state) : «dfn'DIVU» (7,1,2) (fixture s 0 17 18446744073709551613) = (let t := fixture s 0 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551613 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 0 17 18446744073709551613) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (17 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551613 : BitVec 64))), 7) (fixture s 0 17 18446744073709551613)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551613 : BitVec 64))) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (17 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551613 : BitVec 64))), 7) (fixture s 0 17 18446744073709551613) = _
 have numeric : (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (17 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551613 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_6_0
example (s : riscv_state) : «dfn'DIVU» (0,1,2) (fixture s 0 18446744073709551599 18446744073709551613) = (let t := fixture s 0 18446744073709551599 18446744073709551613; t) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551613 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 0 18446744073709551599 18446744073709551613) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551599 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551613 : BitVec 64))), 0) (fixture s 0 18446744073709551599 18446744073709551613)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551613 : BitVec 64))) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551599 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551613 : BitVec 64))), 0) (fixture s 0 18446744073709551599 18446744073709551613) = _
 have numeric : (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551599 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551613 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_6_1
example (s : riscv_state) : «dfn'DIVU» (1,1,2) (fixture s 0 18446744073709551599 18446744073709551613) = (let t := fixture s 0 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551613 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 0 18446744073709551599 18446744073709551613) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551599 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551613 : BitVec 64))), 1) (fixture s 0 18446744073709551599 18446744073709551613)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551613 : BitVec 64))) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551599 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551613 : BitVec 64))), 1) (fixture s 0 18446744073709551599 18446744073709551613) = _
 have numeric : (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551599 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551613 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_6_2
example (s : riscv_state) : «dfn'DIVU» (2,1,2) (fixture s 0 18446744073709551599 18446744073709551613) = (let t := fixture s 0 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551613 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 0 18446744073709551599 18446744073709551613) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551599 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551613 : BitVec 64))), 2) (fixture s 0 18446744073709551599 18446744073709551613)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551613 : BitVec 64))) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551599 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551613 : BitVec 64))), 2) (fixture s 0 18446744073709551599 18446744073709551613) = _
 have numeric : (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551599 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551613 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_6_7
example (s : riscv_state) : «dfn'DIVU» (7,1,2) (fixture s 0 18446744073709551599 18446744073709551613) = (let t := fixture s 0 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551613 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 0 18446744073709551599 18446744073709551613) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551599 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551613 : BitVec 64))), 7) (fixture s 0 18446744073709551599 18446744073709551613)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551613 : BitVec 64))) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551599 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551613 : BitVec 64))), 7) (fixture s 0 18446744073709551599 18446744073709551613) = _
 have numeric : (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551599 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551613 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_7_0
example (s : riscv_state) : «dfn'DIVU» (0,1,2) (fixture s 0 9223372036854775808 18446744073709551615) = (let t := fixture s 0 9223372036854775808 18446744073709551615; t) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 0 9223372036854775808 18446744073709551615) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))), 0) (fixture s 0 9223372036854775808 18446744073709551615)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))), 0) (fixture s 0 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_7_1
example (s : riscv_state) : «dfn'DIVU» (1,1,2) (fixture s 0 9223372036854775808 18446744073709551615) = (let t := fixture s 0 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 0 9223372036854775808 18446744073709551615) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))), 1) (fixture s 0 9223372036854775808 18446744073709551615)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))), 1) (fixture s 0 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_7_2
example (s : riscv_state) : «dfn'DIVU» (2,1,2) (fixture s 0 9223372036854775808 18446744073709551615) = (let t := fixture s 0 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 0 9223372036854775808 18446744073709551615) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))), 2) (fixture s 0 9223372036854775808 18446744073709551615)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))), 2) (fixture s 0 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_7_7
example (s : riscv_state) : «dfn'DIVU» (7,1,2) (fixture s 0 9223372036854775808 18446744073709551615) = (let t := fixture s 0 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 0 9223372036854775808 18446744073709551615) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))), 7) (fixture s 0 9223372036854775808 18446744073709551615)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))), 7) (fixture s 0 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_8_0
example (s : riscv_state) : «dfn'DIVU» (0,1,2) (fixture s 0 2147483648 4294967295) = (let t := fixture s 0 2147483648 4294967295; t) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967295 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 0 2147483648 4294967295) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967295 : BitVec 64))), 0) (fixture s 0 2147483648 4294967295)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967295 : BitVec 64))) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967295 : BitVec 64))), 0) (fixture s 0 2147483648 4294967295) = _
 have numeric : (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967295 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_8_1
example (s : riscv_state) : «dfn'DIVU» (1,1,2) (fixture s 0 2147483648 4294967295) = (let t := fixture s 0 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967295 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 0 2147483648 4294967295) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967295 : BitVec 64))), 1) (fixture s 0 2147483648 4294967295)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967295 : BitVec 64))) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967295 : BitVec 64))), 1) (fixture s 0 2147483648 4294967295) = _
 have numeric : (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967295 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_8_2
example (s : riscv_state) : «dfn'DIVU» (2,1,2) (fixture s 0 2147483648 4294967295) = (let t := fixture s 0 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967295 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 0 2147483648 4294967295) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967295 : BitVec 64))), 2) (fixture s 0 2147483648 4294967295)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967295 : BitVec 64))) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967295 : BitVec 64))), 2) (fixture s 0 2147483648 4294967295) = _
 have numeric : (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967295 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_8_7
example (s : riscv_state) : «dfn'DIVU» (7,1,2) (fixture s 0 2147483648 4294967295) = (let t := fixture s 0 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967295 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 0 2147483648 4294967295) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967295 : BitVec 64))), 7) (fixture s 0 2147483648 4294967295)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967295 : BitVec 64))) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967295 : BitVec 64))), 7) (fixture s 0 2147483648 4294967295) = _
 have numeric : (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (2147483648 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967295 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_9_0
example (s : riscv_state) : «dfn'DIVU» (0,1,2) (fixture s 0 4294967313 4294967296) = (let t := fixture s 0 4294967313 4294967296; t) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967296 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 0 4294967313 4294967296) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967313 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967296 : BitVec 64))), 0) (fixture s 0 4294967313 4294967296)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967296 : BitVec 64))) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 0 4294967313 4294967296) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_9_1
example (s : riscv_state) : «dfn'DIVU» (1,1,2) (fixture s 0 4294967313 4294967296) = (let t := fixture s 0 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967296 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 0 4294967313 4294967296) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967313 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967296 : BitVec 64))), 1) (fixture s 0 4294967313 4294967296)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967296 : BitVec 64))) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 0 4294967313 4294967296) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_9_2
example (s : riscv_state) : «dfn'DIVU» (2,1,2) (fixture s 0 4294967313 4294967296) = (let t := fixture s 0 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967296 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 0 4294967313 4294967296) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967313 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967296 : BitVec 64))), 2) (fixture s 0 4294967313 4294967296)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967296 : BitVec 64))) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 0 4294967313 4294967296) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_9_7
example (s : riscv_state) : «dfn'DIVU» (7,1,2) (fixture s 0 4294967313 4294967296) = (let t := fixture s 0 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967296 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 0 4294967313 4294967296) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967313 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967296 : BitVec 64))), 7) (fixture s 0 4294967313 4294967296)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (4294967296 : BitVec 64))) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 0 4294967313 4294967296) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_10_0
example (s : riscv_state) : «dfn'DIVU» (0,1,2) (fixture s 0 18446744073709551615 2) = (let t := fixture s 0 18446744073709551615 2; t) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (2 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 0 18446744073709551615 2) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (2 : BitVec 64))), 0) (fixture s 0 18446744073709551615 2)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (2 : BitVec 64))) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (2 : BitVec 64))), 0) (fixture s 0 18446744073709551615 2) = _
 have numeric : (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (2 : BitVec 64)))) = (2147483647 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_10_1
example (s : riscv_state) : «dfn'DIVU» (1,1,2) (fixture s 0 18446744073709551615 2) = (let t := fixture s 0 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 1 2147483647 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (2 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 0 18446744073709551615 2) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (2 : BitVec 64))), 1) (fixture s 0 18446744073709551615 2)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (2 : BitVec 64))) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (2 : BitVec 64))), 1) (fixture s 0 18446744073709551615 2) = _
 have numeric : (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (2 : BitVec 64)))) = (2147483647 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_10_2
example (s : riscv_state) : «dfn'DIVU» (2,1,2) (fixture s 0 18446744073709551615 2) = (let t := fixture s 0 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 2 2147483647 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (2 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 0 18446744073709551615 2) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (2 : BitVec 64))), 2) (fixture s 0 18446744073709551615 2)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (2 : BitVec 64))) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (2 : BitVec 64))), 2) (fixture s 0 18446744073709551615 2) = _
 have numeric : (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (2 : BitVec 64)))) = (2147483647 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_10_7
example (s : riscv_state) : «dfn'DIVU» (7,1,2) (fixture s 0 18446744073709551615 2) = (let t := fixture s 0 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 7 2147483647 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (2 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 0 18446744073709551615 2) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (2 : BitVec 64))), 7) (fixture s 0 18446744073709551615 2)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (2 : BitVec 64))) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (2 : BitVec 64))), 7) (fixture s 0 18446744073709551615 2) = _
 have numeric : (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (2 : BitVec 64)))) = (2147483647 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_11_0
example (s : riscv_state) : «dfn'DIVU» (0,1,2) (fixture s 0 18446744073709551615 3) = (let t := fixture s 0 18446744073709551615 3; t) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 0 18446744073709551615 3) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))), 0) (fixture s 0 18446744073709551615 3)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))), 0) (fixture s 0 18446744073709551615 3) = _
 have numeric : (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64)))) = (1431655765 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_11_1
example (s : riscv_state) : «dfn'DIVU» (1,1,2) (fixture s 0 18446744073709551615 3) = (let t := fixture s 0 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 1 1431655765 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 0 18446744073709551615 3) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))), 1) (fixture s 0 18446744073709551615 3)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))), 1) (fixture s 0 18446744073709551615 3) = _
 have numeric : (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64)))) = (1431655765 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_11_2
example (s : riscv_state) : «dfn'DIVU» (2,1,2) (fixture s 0 18446744073709551615 3) = (let t := fixture s 0 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 2 1431655765 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 0 18446744073709551615 3) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))), 2) (fixture s 0 18446744073709551615 3)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))), 2) (fixture s 0 18446744073709551615 3) = _
 have numeric : (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64)))) = (1431655765 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_11_7
example (s : riscv_state) : «dfn'DIVU» (7,1,2) (fixture s 0 18446744073709551615 3) = (let t := fixture s 0 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 7 1431655765 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 0 18446744073709551615 3) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))), 7) (fixture s 0 18446744073709551615 3)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))), 7) (fixture s 0 18446744073709551615 3) = _
 have numeric : (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64)))) = (1431655765 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_12_0
example (s : riscv_state) : «dfn'DIVU» (0,0,2) (fixture s 0 17 3) = (let t := fixture s 0 17 3; t) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 0 17 3) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))), 0) (fixture s 0 17 3)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))), 0) (fixture s 0 17 3) = _
 have numeric : (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_12_1
example (s : riscv_state) : «dfn'DIVU» (1,0,2) (fixture s 0 17 3) = (let t := fixture s 0 17 3; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 0 17 3) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))), 1) (fixture s 0 17 3)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))), 1) (fixture s 0 17 3) = _
 have numeric : (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_12_2
example (s : riscv_state) : «dfn'DIVU» (2,0,2) (fixture s 0 17 3) = (let t := fixture s 0 17 3; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 0 17 3) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))), 2) (fixture s 0 17 3)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))), 2) (fixture s 0 17 3) = _
 have numeric : (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_12_7
example (s : riscv_state) : «dfn'DIVU» (7,0,2) (fixture s 0 17 3) = (let t := fixture s 0 17 3; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 0 17 3) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))), 7) (fixture s 0 17 3)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64))), 7) (fixture s 0 17 3) = _
 have numeric : (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (3 : BitVec 64)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_13_0
example (s : riscv_state) : «dfn'DIVU» (0,1,0) (fixture s 0 18446744073709551615 3) = (let t := fixture s 0 18446744073709551615 3; t) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 0 18446744073709551615 3) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))), 0) (fixture s 0 18446744073709551615 3)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 0 18446744073709551615 3) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_13_1
example (s : riscv_state) : «dfn'DIVU» (1,1,0) (fixture s 0 18446744073709551615 3) = (let t := fixture s 0 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 0 18446744073709551615 3) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))), 1) (fixture s 0 18446744073709551615 3)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 0 18446744073709551615 3) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_13_2
example (s : riscv_state) : «dfn'DIVU» (2,1,0) (fixture s 0 18446744073709551615 3) = (let t := fixture s 0 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 0 18446744073709551615 3) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))), 2) (fixture s 0 18446744073709551615 3)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 0 18446744073709551615 3) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_13_7
example (s : riscv_state) : «dfn'DIVU» (7,1,0) (fixture s 0 18446744073709551615 3) = (let t := fixture s 0 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 0 18446744073709551615 3) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (18446744073709551615 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))), 7) (fixture s 0 18446744073709551615 3)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (0 : BitVec 64))) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 0 18446744073709551615 3) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_14_0
example (s : riscv_state) : «dfn'DIVU» (0,1,1) (fixture s 0 9223372036854775808 2) = (let t := fixture s 0 9223372036854775808 2; t) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 0 9223372036854775808 2) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))), 0) (fixture s 0 9223372036854775808 2)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 0 9223372036854775808 2) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_14_1
example (s : riscv_state) : «dfn'DIVU» (1,1,1) (fixture s 0 9223372036854775808 2) = (let t := fixture s 0 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 0 9223372036854775808 2) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))), 1) (fixture s 0 9223372036854775808 2)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 0 9223372036854775808 2) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_14_2
example (s : riscv_state) : «dfn'DIVU» (2,1,1) (fixture s 0 9223372036854775808 2) = (let t := fixture s 0 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 0 9223372036854775808 2) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))), 2) (fixture s 0 9223372036854775808 2)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 0 9223372036854775808 2) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_0_14_7
example (s : riscv_state) : «dfn'DIVU» (7,1,1) (fixture s 0 9223372036854775808 2) = (let t := fixture s 0 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((BitVec.setWidth 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 0 9223372036854775808 2) else «write'GPR» (BitVec.udiv (BitVec.setWidth 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) (BitVec.setWidth 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))), 7) (fixture s 0 9223372036854775808 2)) = _
 have divisorZero : ((BitVec.setWidth 64 (holWordExtract 32 31 0 (9223372036854775808 : BitVec 64))) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 0 9223372036854775808 2) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_0_0
example (s : riscv_state) : «dfn'DIVU» (0,1,2) (fixture s 2 0 0) = (let t := fixture s 2 0 0; t) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 2 0 0) else «write'GPR» (BitVec.udiv (0 : BitVec 64) (0 : BitVec 64), 0) (fixture s 2 0 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 2 0 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_0_1
example (s : riscv_state) : «dfn'DIVU» (1,1,2) (fixture s 2 0 0) = (let t := fixture s 2 0 0; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 2 0 0) else «write'GPR» (BitVec.udiv (0 : BitVec 64) (0 : BitVec 64), 1) (fixture s 2 0 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 2 0 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_0_2
example (s : riscv_state) : «dfn'DIVU» (2,1,2) (fixture s 2 0 0) = (let t := fixture s 2 0 0; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 2 0 0) else «write'GPR» (BitVec.udiv (0 : BitVec 64) (0 : BitVec 64), 2) (fixture s 2 0 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 2 0 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_0_7
example (s : riscv_state) : «dfn'DIVU» (7,1,2) (fixture s 2 0 0) = (let t := fixture s 2 0 0; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 2 0 0) else «write'GPR» (BitVec.udiv (0 : BitVec 64) (0 : BitVec 64), 7) (fixture s 2 0 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 2 0 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_1_0
example (s : riscv_state) : «dfn'DIVU» (0,1,2) (fixture s 2 17 0) = (let t := fixture s 2 17 0; t) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 2 17 0) else «write'GPR» (BitVec.udiv (17 : BitVec 64) (0 : BitVec 64), 0) (fixture s 2 17 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 2 17 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_1_1
example (s : riscv_state) : «dfn'DIVU» (1,1,2) (fixture s 2 17 0) = (let t := fixture s 2 17 0; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 2 17 0) else «write'GPR» (BitVec.udiv (17 : BitVec 64) (0 : BitVec 64), 1) (fixture s 2 17 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 2 17 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_1_2
example (s : riscv_state) : «dfn'DIVU» (2,1,2) (fixture s 2 17 0) = (let t := fixture s 2 17 0; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 2 17 0) else «write'GPR» (BitVec.udiv (17 : BitVec 64) (0 : BitVec 64), 2) (fixture s 2 17 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 2 17 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_1_7
example (s : riscv_state) : «dfn'DIVU» (7,1,2) (fixture s 2 17 0) = (let t := fixture s 2 17 0; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 2 17 0) else «write'GPR» (BitVec.udiv (17 : BitVec 64) (0 : BitVec 64), 7) (fixture s 2 17 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 2 17 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_2_0
example (s : riscv_state) : «dfn'DIVU» (0,1,2) (fixture s 2 18446744073709551615 0) = (let t := fixture s 2 18446744073709551615 0; t) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 2 18446744073709551615 0) else «write'GPR» (BitVec.udiv (18446744073709551615 : BitVec 64) (0 : BitVec 64), 0) (fixture s 2 18446744073709551615 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 2 18446744073709551615 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_2_1
example (s : riscv_state) : «dfn'DIVU» (1,1,2) (fixture s 2 18446744073709551615 0) = (let t := fixture s 2 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 2 18446744073709551615 0) else «write'GPR» (BitVec.udiv (18446744073709551615 : BitVec 64) (0 : BitVec 64), 1) (fixture s 2 18446744073709551615 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 2 18446744073709551615 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_2_2
example (s : riscv_state) : «dfn'DIVU» (2,1,2) (fixture s 2 18446744073709551615 0) = (let t := fixture s 2 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 2 18446744073709551615 0) else «write'GPR» (BitVec.udiv (18446744073709551615 : BitVec 64) (0 : BitVec 64), 2) (fixture s 2 18446744073709551615 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 2 18446744073709551615 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_2_7
example (s : riscv_state) : «dfn'DIVU» (7,1,2) (fixture s 2 18446744073709551615 0) = (let t := fixture s 2 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 2 18446744073709551615 0) else «write'GPR» (BitVec.udiv (18446744073709551615 : BitVec 64) (0 : BitVec 64), 7) (fixture s 2 18446744073709551615 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 2 18446744073709551615 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_3_0
example (s : riscv_state) : «dfn'DIVU» (0,1,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; t) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 2 17 3) else «write'GPR» (BitVec.udiv (17 : BitVec 64) (3 : BitVec 64), 0) (fixture s 2 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (17 : BitVec 64) (3 : BitVec 64), 0) (fixture s 2 17 3) = _
 have numeric : (BitVec.udiv (17 : BitVec 64) (3 : BitVec 64)) = (5 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_3_1
example (s : riscv_state) : «dfn'DIVU» (1,1,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; {t with c_gpr := holUpdate 7 (holUpdate 1 5 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 2 17 3) else «write'GPR» (BitVec.udiv (17 : BitVec 64) (3 : BitVec 64), 1) (fixture s 2 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (17 : BitVec 64) (3 : BitVec 64), 1) (fixture s 2 17 3) = _
 have numeric : (BitVec.udiv (17 : BitVec 64) (3 : BitVec 64)) = (5 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_3_2
example (s : riscv_state) : «dfn'DIVU» (2,1,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; {t with c_gpr := holUpdate 7 (holUpdate 2 5 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 2 17 3) else «write'GPR» (BitVec.udiv (17 : BitVec 64) (3 : BitVec 64), 2) (fixture s 2 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (17 : BitVec 64) (3 : BitVec 64), 2) (fixture s 2 17 3) = _
 have numeric : (BitVec.udiv (17 : BitVec 64) (3 : BitVec 64)) = (5 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_3_7
example (s : riscv_state) : «dfn'DIVU» (7,1,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; {t with c_gpr := holUpdate 7 (holUpdate 7 5 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 2 17 3) else «write'GPR» (BitVec.udiv (17 : BitVec 64) (3 : BitVec 64), 7) (fixture s 2 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (17 : BitVec 64) (3 : BitVec 64), 7) (fixture s 2 17 3) = _
 have numeric : (BitVec.udiv (17 : BitVec 64) (3 : BitVec 64)) = (5 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_4_0
example (s : riscv_state) : «dfn'DIVU» (0,1,2) (fixture s 2 18446744073709551599 3) = (let t := fixture s 2 18446744073709551599 3; t) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 2 18446744073709551599 3) else «write'GPR» (BitVec.udiv (18446744073709551599 : BitVec 64) (3 : BitVec 64), 0) (fixture s 2 18446744073709551599 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (18446744073709551599 : BitVec 64) (3 : BitVec 64), 0) (fixture s 2 18446744073709551599 3) = _
 have numeric : (BitVec.udiv (18446744073709551599 : BitVec 64) (3 : BitVec 64)) = (6148914691236517199 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_4_1
example (s : riscv_state) : «dfn'DIVU» (1,1,2) (fixture s 2 18446744073709551599 3) = (let t := fixture s 2 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 1 6148914691236517199 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 2 18446744073709551599 3) else «write'GPR» (BitVec.udiv (18446744073709551599 : BitVec 64) (3 : BitVec 64), 1) (fixture s 2 18446744073709551599 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (18446744073709551599 : BitVec 64) (3 : BitVec 64), 1) (fixture s 2 18446744073709551599 3) = _
 have numeric : (BitVec.udiv (18446744073709551599 : BitVec 64) (3 : BitVec 64)) = (6148914691236517199 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_4_2
example (s : riscv_state) : «dfn'DIVU» (2,1,2) (fixture s 2 18446744073709551599 3) = (let t := fixture s 2 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 2 6148914691236517199 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 2 18446744073709551599 3) else «write'GPR» (BitVec.udiv (18446744073709551599 : BitVec 64) (3 : BitVec 64), 2) (fixture s 2 18446744073709551599 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (18446744073709551599 : BitVec 64) (3 : BitVec 64), 2) (fixture s 2 18446744073709551599 3) = _
 have numeric : (BitVec.udiv (18446744073709551599 : BitVec 64) (3 : BitVec 64)) = (6148914691236517199 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_4_7
example (s : riscv_state) : «dfn'DIVU» (7,1,2) (fixture s 2 18446744073709551599 3) = (let t := fixture s 2 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 7 6148914691236517199 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 2 18446744073709551599 3) else «write'GPR» (BitVec.udiv (18446744073709551599 : BitVec 64) (3 : BitVec 64), 7) (fixture s 2 18446744073709551599 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (18446744073709551599 : BitVec 64) (3 : BitVec 64), 7) (fixture s 2 18446744073709551599 3) = _
 have numeric : (BitVec.udiv (18446744073709551599 : BitVec 64) (3 : BitVec 64)) = (6148914691236517199 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_5_0
example (s : riscv_state) : «dfn'DIVU» (0,1,2) (fixture s 2 17 18446744073709551613) = (let t := fixture s 2 17 18446744073709551613; t) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 2 17 18446744073709551613) else «write'GPR» (BitVec.udiv (17 : BitVec 64) (18446744073709551613 : BitVec 64), 0) (fixture s 2 17 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (17 : BitVec 64) (18446744073709551613 : BitVec 64), 0) (fixture s 2 17 18446744073709551613) = _
 have numeric : (BitVec.udiv (17 : BitVec 64) (18446744073709551613 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_5_1
example (s : riscv_state) : «dfn'DIVU» (1,1,2) (fixture s 2 17 18446744073709551613) = (let t := fixture s 2 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 2 17 18446744073709551613) else «write'GPR» (BitVec.udiv (17 : BitVec 64) (18446744073709551613 : BitVec 64), 1) (fixture s 2 17 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (17 : BitVec 64) (18446744073709551613 : BitVec 64), 1) (fixture s 2 17 18446744073709551613) = _
 have numeric : (BitVec.udiv (17 : BitVec 64) (18446744073709551613 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_5_2
example (s : riscv_state) : «dfn'DIVU» (2,1,2) (fixture s 2 17 18446744073709551613) = (let t := fixture s 2 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 2 17 18446744073709551613) else «write'GPR» (BitVec.udiv (17 : BitVec 64) (18446744073709551613 : BitVec 64), 2) (fixture s 2 17 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (17 : BitVec 64) (18446744073709551613 : BitVec 64), 2) (fixture s 2 17 18446744073709551613) = _
 have numeric : (BitVec.udiv (17 : BitVec 64) (18446744073709551613 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_5_7
example (s : riscv_state) : «dfn'DIVU» (7,1,2) (fixture s 2 17 18446744073709551613) = (let t := fixture s 2 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 2 17 18446744073709551613) else «write'GPR» (BitVec.udiv (17 : BitVec 64) (18446744073709551613 : BitVec 64), 7) (fixture s 2 17 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (17 : BitVec 64) (18446744073709551613 : BitVec 64), 7) (fixture s 2 17 18446744073709551613) = _
 have numeric : (BitVec.udiv (17 : BitVec 64) (18446744073709551613 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_6_0
example (s : riscv_state) : «dfn'DIVU» (0,1,2) (fixture s 2 18446744073709551599 18446744073709551613) = (let t := fixture s 2 18446744073709551599 18446744073709551613; t) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 2 18446744073709551599 18446744073709551613) else «write'GPR» (BitVec.udiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 0) (fixture s 2 18446744073709551599 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 0) (fixture s 2 18446744073709551599 18446744073709551613) = _
 have numeric : (BitVec.udiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_6_1
example (s : riscv_state) : «dfn'DIVU» (1,1,2) (fixture s 2 18446744073709551599 18446744073709551613) = (let t := fixture s 2 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 2 18446744073709551599 18446744073709551613) else «write'GPR» (BitVec.udiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 1) (fixture s 2 18446744073709551599 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 1) (fixture s 2 18446744073709551599 18446744073709551613) = _
 have numeric : (BitVec.udiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_6_2
example (s : riscv_state) : «dfn'DIVU» (2,1,2) (fixture s 2 18446744073709551599 18446744073709551613) = (let t := fixture s 2 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 2 18446744073709551599 18446744073709551613) else «write'GPR» (BitVec.udiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 2) (fixture s 2 18446744073709551599 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 2) (fixture s 2 18446744073709551599 18446744073709551613) = _
 have numeric : (BitVec.udiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_6_7
example (s : riscv_state) : «dfn'DIVU» (7,1,2) (fixture s 2 18446744073709551599 18446744073709551613) = (let t := fixture s 2 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 2 18446744073709551599 18446744073709551613) else «write'GPR» (BitVec.udiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 7) (fixture s 2 18446744073709551599 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 7) (fixture s 2 18446744073709551599 18446744073709551613) = _
 have numeric : (BitVec.udiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_7_0
example (s : riscv_state) : «dfn'DIVU» (0,1,2) (fixture s 2 9223372036854775808 18446744073709551615) = (let t := fixture s 2 9223372036854775808 18446744073709551615; t) := by
 change (if ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 2 9223372036854775808 18446744073709551615) else «write'GPR» (BitVec.udiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 0) (fixture s 2 9223372036854775808 18446744073709551615)) = _
 have divisorZero : ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 0) (fixture s 2 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.udiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_7_1
example (s : riscv_state) : «dfn'DIVU» (1,1,2) (fixture s 2 9223372036854775808 18446744073709551615) = (let t := fixture s 2 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 2 9223372036854775808 18446744073709551615) else «write'GPR» (BitVec.udiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 1) (fixture s 2 9223372036854775808 18446744073709551615)) = _
 have divisorZero : ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 1) (fixture s 2 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.udiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_7_2
example (s : riscv_state) : «dfn'DIVU» (2,1,2) (fixture s 2 9223372036854775808 18446744073709551615) = (let t := fixture s 2 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 2 9223372036854775808 18446744073709551615) else «write'GPR» (BitVec.udiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 2) (fixture s 2 9223372036854775808 18446744073709551615)) = _
 have divisorZero : ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 2) (fixture s 2 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.udiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_7_7
example (s : riscv_state) : «dfn'DIVU» (7,1,2) (fixture s 2 9223372036854775808 18446744073709551615) = (let t := fixture s 2 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 2 9223372036854775808 18446744073709551615) else «write'GPR» (BitVec.udiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 7) (fixture s 2 9223372036854775808 18446744073709551615)) = _
 have divisorZero : ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 7) (fixture s 2 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.udiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_8_0
example (s : riscv_state) : «dfn'DIVU» (0,1,2) (fixture s 2 2147483648 4294967295) = (let t := fixture s 2 2147483648 4294967295; t) := by
 change (if ((4294967295 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 2 2147483648 4294967295) else «write'GPR» (BitVec.udiv (2147483648 : BitVec 64) (4294967295 : BitVec 64), 0) (fixture s 2 2147483648 4294967295)) = _
 have divisorZero : ((4294967295 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (2147483648 : BitVec 64) (4294967295 : BitVec 64), 0) (fixture s 2 2147483648 4294967295) = _
 have numeric : (BitVec.udiv (2147483648 : BitVec 64) (4294967295 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_8_1
example (s : riscv_state) : «dfn'DIVU» (1,1,2) (fixture s 2 2147483648 4294967295) = (let t := fixture s 2 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967295 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 2 2147483648 4294967295) else «write'GPR» (BitVec.udiv (2147483648 : BitVec 64) (4294967295 : BitVec 64), 1) (fixture s 2 2147483648 4294967295)) = _
 have divisorZero : ((4294967295 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (2147483648 : BitVec 64) (4294967295 : BitVec 64), 1) (fixture s 2 2147483648 4294967295) = _
 have numeric : (BitVec.udiv (2147483648 : BitVec 64) (4294967295 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_8_2
example (s : riscv_state) : «dfn'DIVU» (2,1,2) (fixture s 2 2147483648 4294967295) = (let t := fixture s 2 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967295 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 2 2147483648 4294967295) else «write'GPR» (BitVec.udiv (2147483648 : BitVec 64) (4294967295 : BitVec 64), 2) (fixture s 2 2147483648 4294967295)) = _
 have divisorZero : ((4294967295 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (2147483648 : BitVec 64) (4294967295 : BitVec 64), 2) (fixture s 2 2147483648 4294967295) = _
 have numeric : (BitVec.udiv (2147483648 : BitVec 64) (4294967295 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_8_7
example (s : riscv_state) : «dfn'DIVU» (7,1,2) (fixture s 2 2147483648 4294967295) = (let t := fixture s 2 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967295 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 2 2147483648 4294967295) else «write'GPR» (BitVec.udiv (2147483648 : BitVec 64) (4294967295 : BitVec 64), 7) (fixture s 2 2147483648 4294967295)) = _
 have divisorZero : ((4294967295 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (2147483648 : BitVec 64) (4294967295 : BitVec 64), 7) (fixture s 2 2147483648 4294967295) = _
 have numeric : (BitVec.udiv (2147483648 : BitVec 64) (4294967295 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_9_0
example (s : riscv_state) : «dfn'DIVU» (0,1,2) (fixture s 2 4294967313 4294967296) = (let t := fixture s 2 4294967313 4294967296; t) := by
 change (if ((4294967296 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 2 4294967313 4294967296) else «write'GPR» (BitVec.udiv (4294967313 : BitVec 64) (4294967296 : BitVec 64), 0) (fixture s 2 4294967313 4294967296)) = _
 have divisorZero : ((4294967296 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (4294967313 : BitVec 64) (4294967296 : BitVec 64), 0) (fixture s 2 4294967313 4294967296) = _
 have numeric : (BitVec.udiv (4294967313 : BitVec 64) (4294967296 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_9_1
example (s : riscv_state) : «dfn'DIVU» (1,1,2) (fixture s 2 4294967313 4294967296) = (let t := fixture s 2 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967296 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 2 4294967313 4294967296) else «write'GPR» (BitVec.udiv (4294967313 : BitVec 64) (4294967296 : BitVec 64), 1) (fixture s 2 4294967313 4294967296)) = _
 have divisorZero : ((4294967296 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (4294967313 : BitVec 64) (4294967296 : BitVec 64), 1) (fixture s 2 4294967313 4294967296) = _
 have numeric : (BitVec.udiv (4294967313 : BitVec 64) (4294967296 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_9_2
example (s : riscv_state) : «dfn'DIVU» (2,1,2) (fixture s 2 4294967313 4294967296) = (let t := fixture s 2 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967296 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 2 4294967313 4294967296) else «write'GPR» (BitVec.udiv (4294967313 : BitVec 64) (4294967296 : BitVec 64), 2) (fixture s 2 4294967313 4294967296)) = _
 have divisorZero : ((4294967296 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (4294967313 : BitVec 64) (4294967296 : BitVec 64), 2) (fixture s 2 4294967313 4294967296) = _
 have numeric : (BitVec.udiv (4294967313 : BitVec 64) (4294967296 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_9_7
example (s : riscv_state) : «dfn'DIVU» (7,1,2) (fixture s 2 4294967313 4294967296) = (let t := fixture s 2 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967296 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 2 4294967313 4294967296) else «write'GPR» (BitVec.udiv (4294967313 : BitVec 64) (4294967296 : BitVec 64), 7) (fixture s 2 4294967313 4294967296)) = _
 have divisorZero : ((4294967296 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (4294967313 : BitVec 64) (4294967296 : BitVec 64), 7) (fixture s 2 4294967313 4294967296) = _
 have numeric : (BitVec.udiv (4294967313 : BitVec 64) (4294967296 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_10_0
example (s : riscv_state) : «dfn'DIVU» (0,1,2) (fixture s 2 18446744073709551615 2) = (let t := fixture s 2 18446744073709551615 2; t) := by
 change (if ((2 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 2 18446744073709551615 2) else «write'GPR» (BitVec.udiv (18446744073709551615 : BitVec 64) (2 : BitVec 64), 0) (fixture s 2 18446744073709551615 2)) = _
 have divisorZero : ((2 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (18446744073709551615 : BitVec 64) (2 : BitVec 64), 0) (fixture s 2 18446744073709551615 2) = _
 have numeric : (BitVec.udiv (18446744073709551615 : BitVec 64) (2 : BitVec 64)) = (9223372036854775807 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_10_1
example (s : riscv_state) : «dfn'DIVU» (1,1,2) (fixture s 2 18446744073709551615 2) = (let t := fixture s 2 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 1 9223372036854775807 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((2 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 2 18446744073709551615 2) else «write'GPR» (BitVec.udiv (18446744073709551615 : BitVec 64) (2 : BitVec 64), 1) (fixture s 2 18446744073709551615 2)) = _
 have divisorZero : ((2 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (18446744073709551615 : BitVec 64) (2 : BitVec 64), 1) (fixture s 2 18446744073709551615 2) = _
 have numeric : (BitVec.udiv (18446744073709551615 : BitVec 64) (2 : BitVec 64)) = (9223372036854775807 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_10_2
example (s : riscv_state) : «dfn'DIVU» (2,1,2) (fixture s 2 18446744073709551615 2) = (let t := fixture s 2 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 2 9223372036854775807 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((2 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 2 18446744073709551615 2) else «write'GPR» (BitVec.udiv (18446744073709551615 : BitVec 64) (2 : BitVec 64), 2) (fixture s 2 18446744073709551615 2)) = _
 have divisorZero : ((2 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (18446744073709551615 : BitVec 64) (2 : BitVec 64), 2) (fixture s 2 18446744073709551615 2) = _
 have numeric : (BitVec.udiv (18446744073709551615 : BitVec 64) (2 : BitVec 64)) = (9223372036854775807 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_10_7
example (s : riscv_state) : «dfn'DIVU» (7,1,2) (fixture s 2 18446744073709551615 2) = (let t := fixture s 2 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 7 9223372036854775807 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((2 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 2 18446744073709551615 2) else «write'GPR» (BitVec.udiv (18446744073709551615 : BitVec 64) (2 : BitVec 64), 7) (fixture s 2 18446744073709551615 2)) = _
 have divisorZero : ((2 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (18446744073709551615 : BitVec 64) (2 : BitVec 64), 7) (fixture s 2 18446744073709551615 2) = _
 have numeric : (BitVec.udiv (18446744073709551615 : BitVec 64) (2 : BitVec 64)) = (9223372036854775807 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_11_0
example (s : riscv_state) : «dfn'DIVU» (0,1,2) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; t) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 2 18446744073709551615 3) else «write'GPR» (BitVec.udiv (18446744073709551615 : BitVec 64) (3 : BitVec 64), 0) (fixture s 2 18446744073709551615 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (18446744073709551615 : BitVec 64) (3 : BitVec 64), 0) (fixture s 2 18446744073709551615 3) = _
 have numeric : (BitVec.udiv (18446744073709551615 : BitVec 64) (3 : BitVec 64)) = (6148914691236517205 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_11_1
example (s : riscv_state) : «dfn'DIVU» (1,1,2) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 1 6148914691236517205 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 2 18446744073709551615 3) else «write'GPR» (BitVec.udiv (18446744073709551615 : BitVec 64) (3 : BitVec 64), 1) (fixture s 2 18446744073709551615 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (18446744073709551615 : BitVec 64) (3 : BitVec 64), 1) (fixture s 2 18446744073709551615 3) = _
 have numeric : (BitVec.udiv (18446744073709551615 : BitVec 64) (3 : BitVec 64)) = (6148914691236517205 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_11_2
example (s : riscv_state) : «dfn'DIVU» (2,1,2) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 2 6148914691236517205 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 2 18446744073709551615 3) else «write'GPR» (BitVec.udiv (18446744073709551615 : BitVec 64) (3 : BitVec 64), 2) (fixture s 2 18446744073709551615 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (18446744073709551615 : BitVec 64) (3 : BitVec 64), 2) (fixture s 2 18446744073709551615 3) = _
 have numeric : (BitVec.udiv (18446744073709551615 : BitVec 64) (3 : BitVec 64)) = (6148914691236517205 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_11_7
example (s : riscv_state) : «dfn'DIVU» (7,1,2) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 7 6148914691236517205 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 2 18446744073709551615 3) else «write'GPR» (BitVec.udiv (18446744073709551615 : BitVec 64) (3 : BitVec 64), 7) (fixture s 2 18446744073709551615 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (18446744073709551615 : BitVec 64) (3 : BitVec 64), 7) (fixture s 2 18446744073709551615 3) = _
 have numeric : (BitVec.udiv (18446744073709551615 : BitVec 64) (3 : BitVec 64)) = (6148914691236517205 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_12_0
example (s : riscv_state) : «dfn'DIVU» (0,0,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; t) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 2 17 3) else «write'GPR» (BitVec.udiv (0 : BitVec 64) (3 : BitVec 64), 0) (fixture s 2 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (0 : BitVec 64) (3 : BitVec 64), 0) (fixture s 2 17 3) = _
 have numeric : (BitVec.udiv (0 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_12_1
example (s : riscv_state) : «dfn'DIVU» (1,0,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 2 17 3) else «write'GPR» (BitVec.udiv (0 : BitVec 64) (3 : BitVec 64), 1) (fixture s 2 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (0 : BitVec 64) (3 : BitVec 64), 1) (fixture s 2 17 3) = _
 have numeric : (BitVec.udiv (0 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_12_2
example (s : riscv_state) : «dfn'DIVU» (2,0,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 2 17 3) else «write'GPR» (BitVec.udiv (0 : BitVec 64) (3 : BitVec 64), 2) (fixture s 2 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (0 : BitVec 64) (3 : BitVec 64), 2) (fixture s 2 17 3) = _
 have numeric : (BitVec.udiv (0 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_12_7
example (s : riscv_state) : «dfn'DIVU» (7,0,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 2 17 3) else «write'GPR» (BitVec.udiv (0 : BitVec 64) (3 : BitVec 64), 7) (fixture s 2 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (0 : BitVec 64) (3 : BitVec 64), 7) (fixture s 2 17 3) = _
 have numeric : (BitVec.udiv (0 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_13_0
example (s : riscv_state) : «dfn'DIVU» (0,1,0) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; t) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 2 18446744073709551615 3) else «write'GPR» (BitVec.udiv (18446744073709551615 : BitVec 64) (0 : BitVec 64), 0) (fixture s 2 18446744073709551615 3)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 2 18446744073709551615 3) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_13_1
example (s : riscv_state) : «dfn'DIVU» (1,1,0) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 2 18446744073709551615 3) else «write'GPR» (BitVec.udiv (18446744073709551615 : BitVec 64) (0 : BitVec 64), 1) (fixture s 2 18446744073709551615 3)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 2 18446744073709551615 3) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_13_2
example (s : riscv_state) : «dfn'DIVU» (2,1,0) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 2 18446744073709551615 3) else «write'GPR» (BitVec.udiv (18446744073709551615 : BitVec 64) (0 : BitVec 64), 2) (fixture s 2 18446744073709551615 3)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 2 18446744073709551615 3) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_13_7
example (s : riscv_state) : «dfn'DIVU» (7,1,0) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 2 18446744073709551615 3) else «write'GPR» (BitVec.udiv (18446744073709551615 : BitVec 64) (0 : BitVec 64), 7) (fixture s 2 18446744073709551615 3)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 2 18446744073709551615 3) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_14_0
example (s : riscv_state) : «dfn'DIVU» (0,1,1) (fixture s 2 9223372036854775808 2) = (let t := fixture s 2 9223372036854775808 2; t) := by
 change (if ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 2 9223372036854775808 2) else «write'GPR» (BitVec.udiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 0) (fixture s 2 9223372036854775808 2)) = _
 have divisorZero : ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 0) (fixture s 2 9223372036854775808 2) = _
 have numeric : (BitVec.udiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_14_1
example (s : riscv_state) : «dfn'DIVU» (1,1,1) (fixture s 2 9223372036854775808 2) = (let t := fixture s 2 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 2 9223372036854775808 2) else «write'GPR» (BitVec.udiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 1) (fixture s 2 9223372036854775808 2)) = _
 have divisorZero : ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 1) (fixture s 2 9223372036854775808 2) = _
 have numeric : (BitVec.udiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_14_2
example (s : riscv_state) : «dfn'DIVU» (2,1,1) (fixture s 2 9223372036854775808 2) = (let t := fixture s 2 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 2 9223372036854775808 2) else «write'GPR» (BitVec.udiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 2) (fixture s 2 9223372036854775808 2)) = _
 have divisorZero : ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 2) (fixture s 2 9223372036854775808 2) = _
 have numeric : (BitVec.udiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_2_14_7
example (s : riscv_state) : «dfn'DIVU» (7,1,1) (fixture s 2 9223372036854775808 2) = (let t := fixture s 2 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 2 9223372036854775808 2) else «write'GPR» (BitVec.udiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 7) (fixture s 2 9223372036854775808 2)) = _
 have divisorZero : ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 7) (fixture s 2 9223372036854775808 2) = _
 have numeric : (BitVec.udiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_0_0
example (s : riscv_state) : «dfn'DIVU» (0,1,2) (fixture s 3 0 0) = (let t := fixture s 3 0 0; t) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 3 0 0) else «write'GPR» (BitVec.udiv (0 : BitVec 64) (0 : BitVec 64), 0) (fixture s 3 0 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 3 0 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_0_1
example (s : riscv_state) : «dfn'DIVU» (1,1,2) (fixture s 3 0 0) = (let t := fixture s 3 0 0; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 3 0 0) else «write'GPR» (BitVec.udiv (0 : BitVec 64) (0 : BitVec 64), 1) (fixture s 3 0 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 3 0 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_0_2
example (s : riscv_state) : «dfn'DIVU» (2,1,2) (fixture s 3 0 0) = (let t := fixture s 3 0 0; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 3 0 0) else «write'GPR» (BitVec.udiv (0 : BitVec 64) (0 : BitVec 64), 2) (fixture s 3 0 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 3 0 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_0_7
example (s : riscv_state) : «dfn'DIVU» (7,1,2) (fixture s 3 0 0) = (let t := fixture s 3 0 0; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 3 0 0) else «write'GPR» (BitVec.udiv (0 : BitVec 64) (0 : BitVec 64), 7) (fixture s 3 0 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 3 0 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_1_0
example (s : riscv_state) : «dfn'DIVU» (0,1,2) (fixture s 3 17 0) = (let t := fixture s 3 17 0; t) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 3 17 0) else «write'GPR» (BitVec.udiv (17 : BitVec 64) (0 : BitVec 64), 0) (fixture s 3 17 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 3 17 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_1_1
example (s : riscv_state) : «dfn'DIVU» (1,1,2) (fixture s 3 17 0) = (let t := fixture s 3 17 0; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 3 17 0) else «write'GPR» (BitVec.udiv (17 : BitVec 64) (0 : BitVec 64), 1) (fixture s 3 17 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 3 17 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_1_2
example (s : riscv_state) : «dfn'DIVU» (2,1,2) (fixture s 3 17 0) = (let t := fixture s 3 17 0; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 3 17 0) else «write'GPR» (BitVec.udiv (17 : BitVec 64) (0 : BitVec 64), 2) (fixture s 3 17 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 3 17 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_1_7
example (s : riscv_state) : «dfn'DIVU» (7,1,2) (fixture s 3 17 0) = (let t := fixture s 3 17 0; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 3 17 0) else «write'GPR» (BitVec.udiv (17 : BitVec 64) (0 : BitVec 64), 7) (fixture s 3 17 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 3 17 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_2_0
example (s : riscv_state) : «dfn'DIVU» (0,1,2) (fixture s 3 18446744073709551615 0) = (let t := fixture s 3 18446744073709551615 0; t) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 3 18446744073709551615 0) else «write'GPR» (BitVec.udiv (18446744073709551615 : BitVec 64) (0 : BitVec 64), 0) (fixture s 3 18446744073709551615 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 3 18446744073709551615 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_2_1
example (s : riscv_state) : «dfn'DIVU» (1,1,2) (fixture s 3 18446744073709551615 0) = (let t := fixture s 3 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 3 18446744073709551615 0) else «write'GPR» (BitVec.udiv (18446744073709551615 : BitVec 64) (0 : BitVec 64), 1) (fixture s 3 18446744073709551615 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 3 18446744073709551615 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_2_2
example (s : riscv_state) : «dfn'DIVU» (2,1,2) (fixture s 3 18446744073709551615 0) = (let t := fixture s 3 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 3 18446744073709551615 0) else «write'GPR» (BitVec.udiv (18446744073709551615 : BitVec 64) (0 : BitVec 64), 2) (fixture s 3 18446744073709551615 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 3 18446744073709551615 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_2_7
example (s : riscv_state) : «dfn'DIVU» (7,1,2) (fixture s 3 18446744073709551615 0) = (let t := fixture s 3 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 3 18446744073709551615 0) else «write'GPR» (BitVec.udiv (18446744073709551615 : BitVec 64) (0 : BitVec 64), 7) (fixture s 3 18446744073709551615 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 3 18446744073709551615 0) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_3_0
example (s : riscv_state) : «dfn'DIVU» (0,1,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; t) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 3 17 3) else «write'GPR» (BitVec.udiv (17 : BitVec 64) (3 : BitVec 64), 0) (fixture s 3 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (17 : BitVec 64) (3 : BitVec 64), 0) (fixture s 3 17 3) = _
 have numeric : (BitVec.udiv (17 : BitVec 64) (3 : BitVec 64)) = (5 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_3_1
example (s : riscv_state) : «dfn'DIVU» (1,1,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; {t with c_gpr := holUpdate 7 (holUpdate 1 5 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 3 17 3) else «write'GPR» (BitVec.udiv (17 : BitVec 64) (3 : BitVec 64), 1) (fixture s 3 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (17 : BitVec 64) (3 : BitVec 64), 1) (fixture s 3 17 3) = _
 have numeric : (BitVec.udiv (17 : BitVec 64) (3 : BitVec 64)) = (5 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_3_2
example (s : riscv_state) : «dfn'DIVU» (2,1,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; {t with c_gpr := holUpdate 7 (holUpdate 2 5 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 3 17 3) else «write'GPR» (BitVec.udiv (17 : BitVec 64) (3 : BitVec 64), 2) (fixture s 3 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (17 : BitVec 64) (3 : BitVec 64), 2) (fixture s 3 17 3) = _
 have numeric : (BitVec.udiv (17 : BitVec 64) (3 : BitVec 64)) = (5 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_3_7
example (s : riscv_state) : «dfn'DIVU» (7,1,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; {t with c_gpr := holUpdate 7 (holUpdate 7 5 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 3 17 3) else «write'GPR» (BitVec.udiv (17 : BitVec 64) (3 : BitVec 64), 7) (fixture s 3 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (17 : BitVec 64) (3 : BitVec 64), 7) (fixture s 3 17 3) = _
 have numeric : (BitVec.udiv (17 : BitVec 64) (3 : BitVec 64)) = (5 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_4_0
example (s : riscv_state) : «dfn'DIVU» (0,1,2) (fixture s 3 18446744073709551599 3) = (let t := fixture s 3 18446744073709551599 3; t) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 3 18446744073709551599 3) else «write'GPR» (BitVec.udiv (18446744073709551599 : BitVec 64) (3 : BitVec 64), 0) (fixture s 3 18446744073709551599 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (18446744073709551599 : BitVec 64) (3 : BitVec 64), 0) (fixture s 3 18446744073709551599 3) = _
 have numeric : (BitVec.udiv (18446744073709551599 : BitVec 64) (3 : BitVec 64)) = (6148914691236517199 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_4_1
example (s : riscv_state) : «dfn'DIVU» (1,1,2) (fixture s 3 18446744073709551599 3) = (let t := fixture s 3 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 1 6148914691236517199 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 3 18446744073709551599 3) else «write'GPR» (BitVec.udiv (18446744073709551599 : BitVec 64) (3 : BitVec 64), 1) (fixture s 3 18446744073709551599 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (18446744073709551599 : BitVec 64) (3 : BitVec 64), 1) (fixture s 3 18446744073709551599 3) = _
 have numeric : (BitVec.udiv (18446744073709551599 : BitVec 64) (3 : BitVec 64)) = (6148914691236517199 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_4_2
example (s : riscv_state) : «dfn'DIVU» (2,1,2) (fixture s 3 18446744073709551599 3) = (let t := fixture s 3 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 2 6148914691236517199 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 3 18446744073709551599 3) else «write'GPR» (BitVec.udiv (18446744073709551599 : BitVec 64) (3 : BitVec 64), 2) (fixture s 3 18446744073709551599 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (18446744073709551599 : BitVec 64) (3 : BitVec 64), 2) (fixture s 3 18446744073709551599 3) = _
 have numeric : (BitVec.udiv (18446744073709551599 : BitVec 64) (3 : BitVec 64)) = (6148914691236517199 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_4_7
example (s : riscv_state) : «dfn'DIVU» (7,1,2) (fixture s 3 18446744073709551599 3) = (let t := fixture s 3 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 7 6148914691236517199 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 3 18446744073709551599 3) else «write'GPR» (BitVec.udiv (18446744073709551599 : BitVec 64) (3 : BitVec 64), 7) (fixture s 3 18446744073709551599 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (18446744073709551599 : BitVec 64) (3 : BitVec 64), 7) (fixture s 3 18446744073709551599 3) = _
 have numeric : (BitVec.udiv (18446744073709551599 : BitVec 64) (3 : BitVec 64)) = (6148914691236517199 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_5_0
example (s : riscv_state) : «dfn'DIVU» (0,1,2) (fixture s 3 17 18446744073709551613) = (let t := fixture s 3 17 18446744073709551613; t) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 3 17 18446744073709551613) else «write'GPR» (BitVec.udiv (17 : BitVec 64) (18446744073709551613 : BitVec 64), 0) (fixture s 3 17 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (17 : BitVec 64) (18446744073709551613 : BitVec 64), 0) (fixture s 3 17 18446744073709551613) = _
 have numeric : (BitVec.udiv (17 : BitVec 64) (18446744073709551613 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_5_1
example (s : riscv_state) : «dfn'DIVU» (1,1,2) (fixture s 3 17 18446744073709551613) = (let t := fixture s 3 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 3 17 18446744073709551613) else «write'GPR» (BitVec.udiv (17 : BitVec 64) (18446744073709551613 : BitVec 64), 1) (fixture s 3 17 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (17 : BitVec 64) (18446744073709551613 : BitVec 64), 1) (fixture s 3 17 18446744073709551613) = _
 have numeric : (BitVec.udiv (17 : BitVec 64) (18446744073709551613 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_5_2
example (s : riscv_state) : «dfn'DIVU» (2,1,2) (fixture s 3 17 18446744073709551613) = (let t := fixture s 3 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 3 17 18446744073709551613) else «write'GPR» (BitVec.udiv (17 : BitVec 64) (18446744073709551613 : BitVec 64), 2) (fixture s 3 17 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (17 : BitVec 64) (18446744073709551613 : BitVec 64), 2) (fixture s 3 17 18446744073709551613) = _
 have numeric : (BitVec.udiv (17 : BitVec 64) (18446744073709551613 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_5_7
example (s : riscv_state) : «dfn'DIVU» (7,1,2) (fixture s 3 17 18446744073709551613) = (let t := fixture s 3 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 3 17 18446744073709551613) else «write'GPR» (BitVec.udiv (17 : BitVec 64) (18446744073709551613 : BitVec 64), 7) (fixture s 3 17 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (17 : BitVec 64) (18446744073709551613 : BitVec 64), 7) (fixture s 3 17 18446744073709551613) = _
 have numeric : (BitVec.udiv (17 : BitVec 64) (18446744073709551613 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_6_0
example (s : riscv_state) : «dfn'DIVU» (0,1,2) (fixture s 3 18446744073709551599 18446744073709551613) = (let t := fixture s 3 18446744073709551599 18446744073709551613; t) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 3 18446744073709551599 18446744073709551613) else «write'GPR» (BitVec.udiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 0) (fixture s 3 18446744073709551599 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 0) (fixture s 3 18446744073709551599 18446744073709551613) = _
 have numeric : (BitVec.udiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_6_1
example (s : riscv_state) : «dfn'DIVU» (1,1,2) (fixture s 3 18446744073709551599 18446744073709551613) = (let t := fixture s 3 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 3 18446744073709551599 18446744073709551613) else «write'GPR» (BitVec.udiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 1) (fixture s 3 18446744073709551599 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 1) (fixture s 3 18446744073709551599 18446744073709551613) = _
 have numeric : (BitVec.udiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_6_2
example (s : riscv_state) : «dfn'DIVU» (2,1,2) (fixture s 3 18446744073709551599 18446744073709551613) = (let t := fixture s 3 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 3 18446744073709551599 18446744073709551613) else «write'GPR» (BitVec.udiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 2) (fixture s 3 18446744073709551599 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 2) (fixture s 3 18446744073709551599 18446744073709551613) = _
 have numeric : (BitVec.udiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_6_7
example (s : riscv_state) : «dfn'DIVU» (7,1,2) (fixture s 3 18446744073709551599 18446744073709551613) = (let t := fixture s 3 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 3 18446744073709551599 18446744073709551613) else «write'GPR» (BitVec.udiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 7) (fixture s 3 18446744073709551599 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 7) (fixture s 3 18446744073709551599 18446744073709551613) = _
 have numeric : (BitVec.udiv (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_7_0
example (s : riscv_state) : «dfn'DIVU» (0,1,2) (fixture s 3 9223372036854775808 18446744073709551615) = (let t := fixture s 3 9223372036854775808 18446744073709551615; t) := by
 change (if ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 3 9223372036854775808 18446744073709551615) else «write'GPR» (BitVec.udiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 0) (fixture s 3 9223372036854775808 18446744073709551615)) = _
 have divisorZero : ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 0) (fixture s 3 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.udiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_7_1
example (s : riscv_state) : «dfn'DIVU» (1,1,2) (fixture s 3 9223372036854775808 18446744073709551615) = (let t := fixture s 3 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 3 9223372036854775808 18446744073709551615) else «write'GPR» (BitVec.udiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 1) (fixture s 3 9223372036854775808 18446744073709551615)) = _
 have divisorZero : ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 1) (fixture s 3 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.udiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_7_2
example (s : riscv_state) : «dfn'DIVU» (2,1,2) (fixture s 3 9223372036854775808 18446744073709551615) = (let t := fixture s 3 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 3 9223372036854775808 18446744073709551615) else «write'GPR» (BitVec.udiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 2) (fixture s 3 9223372036854775808 18446744073709551615)) = _
 have divisorZero : ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 2) (fixture s 3 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.udiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_7_7
example (s : riscv_state) : «dfn'DIVU» (7,1,2) (fixture s 3 9223372036854775808 18446744073709551615) = (let t := fixture s 3 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 3 9223372036854775808 18446744073709551615) else «write'GPR» (BitVec.udiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 7) (fixture s 3 9223372036854775808 18446744073709551615)) = _
 have divisorZero : ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 7) (fixture s 3 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.udiv (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_8_0
example (s : riscv_state) : «dfn'DIVU» (0,1,2) (fixture s 3 2147483648 4294967295) = (let t := fixture s 3 2147483648 4294967295; t) := by
 change (if ((4294967295 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 3 2147483648 4294967295) else «write'GPR» (BitVec.udiv (2147483648 : BitVec 64) (4294967295 : BitVec 64), 0) (fixture s 3 2147483648 4294967295)) = _
 have divisorZero : ((4294967295 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (2147483648 : BitVec 64) (4294967295 : BitVec 64), 0) (fixture s 3 2147483648 4294967295) = _
 have numeric : (BitVec.udiv (2147483648 : BitVec 64) (4294967295 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_8_1
example (s : riscv_state) : «dfn'DIVU» (1,1,2) (fixture s 3 2147483648 4294967295) = (let t := fixture s 3 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967295 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 3 2147483648 4294967295) else «write'GPR» (BitVec.udiv (2147483648 : BitVec 64) (4294967295 : BitVec 64), 1) (fixture s 3 2147483648 4294967295)) = _
 have divisorZero : ((4294967295 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (2147483648 : BitVec 64) (4294967295 : BitVec 64), 1) (fixture s 3 2147483648 4294967295) = _
 have numeric : (BitVec.udiv (2147483648 : BitVec 64) (4294967295 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_8_2
example (s : riscv_state) : «dfn'DIVU» (2,1,2) (fixture s 3 2147483648 4294967295) = (let t := fixture s 3 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967295 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 3 2147483648 4294967295) else «write'GPR» (BitVec.udiv (2147483648 : BitVec 64) (4294967295 : BitVec 64), 2) (fixture s 3 2147483648 4294967295)) = _
 have divisorZero : ((4294967295 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (2147483648 : BitVec 64) (4294967295 : BitVec 64), 2) (fixture s 3 2147483648 4294967295) = _
 have numeric : (BitVec.udiv (2147483648 : BitVec 64) (4294967295 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_8_7
example (s : riscv_state) : «dfn'DIVU» (7,1,2) (fixture s 3 2147483648 4294967295) = (let t := fixture s 3 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967295 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 3 2147483648 4294967295) else «write'GPR» (BitVec.udiv (2147483648 : BitVec 64) (4294967295 : BitVec 64), 7) (fixture s 3 2147483648 4294967295)) = _
 have divisorZero : ((4294967295 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (2147483648 : BitVec 64) (4294967295 : BitVec 64), 7) (fixture s 3 2147483648 4294967295) = _
 have numeric : (BitVec.udiv (2147483648 : BitVec 64) (4294967295 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_9_0
example (s : riscv_state) : «dfn'DIVU» (0,1,2) (fixture s 3 4294967313 4294967296) = (let t := fixture s 3 4294967313 4294967296; t) := by
 change (if ((4294967296 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 3 4294967313 4294967296) else «write'GPR» (BitVec.udiv (4294967313 : BitVec 64) (4294967296 : BitVec 64), 0) (fixture s 3 4294967313 4294967296)) = _
 have divisorZero : ((4294967296 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (4294967313 : BitVec 64) (4294967296 : BitVec 64), 0) (fixture s 3 4294967313 4294967296) = _
 have numeric : (BitVec.udiv (4294967313 : BitVec 64) (4294967296 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_9_1
example (s : riscv_state) : «dfn'DIVU» (1,1,2) (fixture s 3 4294967313 4294967296) = (let t := fixture s 3 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967296 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 3 4294967313 4294967296) else «write'GPR» (BitVec.udiv (4294967313 : BitVec 64) (4294967296 : BitVec 64), 1) (fixture s 3 4294967313 4294967296)) = _
 have divisorZero : ((4294967296 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (4294967313 : BitVec 64) (4294967296 : BitVec 64), 1) (fixture s 3 4294967313 4294967296) = _
 have numeric : (BitVec.udiv (4294967313 : BitVec 64) (4294967296 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_9_2
example (s : riscv_state) : «dfn'DIVU» (2,1,2) (fixture s 3 4294967313 4294967296) = (let t := fixture s 3 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967296 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 3 4294967313 4294967296) else «write'GPR» (BitVec.udiv (4294967313 : BitVec 64) (4294967296 : BitVec 64), 2) (fixture s 3 4294967313 4294967296)) = _
 have divisorZero : ((4294967296 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (4294967313 : BitVec 64) (4294967296 : BitVec 64), 2) (fixture s 3 4294967313 4294967296) = _
 have numeric : (BitVec.udiv (4294967313 : BitVec 64) (4294967296 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_9_7
example (s : riscv_state) : «dfn'DIVU» (7,1,2) (fixture s 3 4294967313 4294967296) = (let t := fixture s 3 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967296 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 3 4294967313 4294967296) else «write'GPR» (BitVec.udiv (4294967313 : BitVec 64) (4294967296 : BitVec 64), 7) (fixture s 3 4294967313 4294967296)) = _
 have divisorZero : ((4294967296 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (4294967313 : BitVec 64) (4294967296 : BitVec 64), 7) (fixture s 3 4294967313 4294967296) = _
 have numeric : (BitVec.udiv (4294967313 : BitVec 64) (4294967296 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_10_0
example (s : riscv_state) : «dfn'DIVU» (0,1,2) (fixture s 3 18446744073709551615 2) = (let t := fixture s 3 18446744073709551615 2; t) := by
 change (if ((2 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 3 18446744073709551615 2) else «write'GPR» (BitVec.udiv (18446744073709551615 : BitVec 64) (2 : BitVec 64), 0) (fixture s 3 18446744073709551615 2)) = _
 have divisorZero : ((2 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (18446744073709551615 : BitVec 64) (2 : BitVec 64), 0) (fixture s 3 18446744073709551615 2) = _
 have numeric : (BitVec.udiv (18446744073709551615 : BitVec 64) (2 : BitVec 64)) = (9223372036854775807 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_10_1
example (s : riscv_state) : «dfn'DIVU» (1,1,2) (fixture s 3 18446744073709551615 2) = (let t := fixture s 3 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 1 9223372036854775807 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((2 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 3 18446744073709551615 2) else «write'GPR» (BitVec.udiv (18446744073709551615 : BitVec 64) (2 : BitVec 64), 1) (fixture s 3 18446744073709551615 2)) = _
 have divisorZero : ((2 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (18446744073709551615 : BitVec 64) (2 : BitVec 64), 1) (fixture s 3 18446744073709551615 2) = _
 have numeric : (BitVec.udiv (18446744073709551615 : BitVec 64) (2 : BitVec 64)) = (9223372036854775807 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_10_2
example (s : riscv_state) : «dfn'DIVU» (2,1,2) (fixture s 3 18446744073709551615 2) = (let t := fixture s 3 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 2 9223372036854775807 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((2 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 3 18446744073709551615 2) else «write'GPR» (BitVec.udiv (18446744073709551615 : BitVec 64) (2 : BitVec 64), 2) (fixture s 3 18446744073709551615 2)) = _
 have divisorZero : ((2 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (18446744073709551615 : BitVec 64) (2 : BitVec 64), 2) (fixture s 3 18446744073709551615 2) = _
 have numeric : (BitVec.udiv (18446744073709551615 : BitVec 64) (2 : BitVec 64)) = (9223372036854775807 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_10_7
example (s : riscv_state) : «dfn'DIVU» (7,1,2) (fixture s 3 18446744073709551615 2) = (let t := fixture s 3 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 7 9223372036854775807 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((2 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 3 18446744073709551615 2) else «write'GPR» (BitVec.udiv (18446744073709551615 : BitVec 64) (2 : BitVec 64), 7) (fixture s 3 18446744073709551615 2)) = _
 have divisorZero : ((2 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (18446744073709551615 : BitVec 64) (2 : BitVec 64), 7) (fixture s 3 18446744073709551615 2) = _
 have numeric : (BitVec.udiv (18446744073709551615 : BitVec 64) (2 : BitVec 64)) = (9223372036854775807 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_11_0
example (s : riscv_state) : «dfn'DIVU» (0,1,2) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; t) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 3 18446744073709551615 3) else «write'GPR» (BitVec.udiv (18446744073709551615 : BitVec 64) (3 : BitVec 64), 0) (fixture s 3 18446744073709551615 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (18446744073709551615 : BitVec 64) (3 : BitVec 64), 0) (fixture s 3 18446744073709551615 3) = _
 have numeric : (BitVec.udiv (18446744073709551615 : BitVec 64) (3 : BitVec 64)) = (6148914691236517205 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_11_1
example (s : riscv_state) : «dfn'DIVU» (1,1,2) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 1 6148914691236517205 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 3 18446744073709551615 3) else «write'GPR» (BitVec.udiv (18446744073709551615 : BitVec 64) (3 : BitVec 64), 1) (fixture s 3 18446744073709551615 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (18446744073709551615 : BitVec 64) (3 : BitVec 64), 1) (fixture s 3 18446744073709551615 3) = _
 have numeric : (BitVec.udiv (18446744073709551615 : BitVec 64) (3 : BitVec 64)) = (6148914691236517205 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_11_2
example (s : riscv_state) : «dfn'DIVU» (2,1,2) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 2 6148914691236517205 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 3 18446744073709551615 3) else «write'GPR» (BitVec.udiv (18446744073709551615 : BitVec 64) (3 : BitVec 64), 2) (fixture s 3 18446744073709551615 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (18446744073709551615 : BitVec 64) (3 : BitVec 64), 2) (fixture s 3 18446744073709551615 3) = _
 have numeric : (BitVec.udiv (18446744073709551615 : BitVec 64) (3 : BitVec 64)) = (6148914691236517205 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_11_7
example (s : riscv_state) : «dfn'DIVU» (7,1,2) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 7 6148914691236517205 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 3 18446744073709551615 3) else «write'GPR» (BitVec.udiv (18446744073709551615 : BitVec 64) (3 : BitVec 64), 7) (fixture s 3 18446744073709551615 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (18446744073709551615 : BitVec 64) (3 : BitVec 64), 7) (fixture s 3 18446744073709551615 3) = _
 have numeric : (BitVec.udiv (18446744073709551615 : BitVec 64) (3 : BitVec 64)) = (6148914691236517205 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_12_0
example (s : riscv_state) : «dfn'DIVU» (0,0,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; t) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 3 17 3) else «write'GPR» (BitVec.udiv (0 : BitVec 64) (3 : BitVec 64), 0) (fixture s 3 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (0 : BitVec 64) (3 : BitVec 64), 0) (fixture s 3 17 3) = _
 have numeric : (BitVec.udiv (0 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_12_1
example (s : riscv_state) : «dfn'DIVU» (1,0,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 3 17 3) else «write'GPR» (BitVec.udiv (0 : BitVec 64) (3 : BitVec 64), 1) (fixture s 3 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (0 : BitVec 64) (3 : BitVec 64), 1) (fixture s 3 17 3) = _
 have numeric : (BitVec.udiv (0 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_12_2
example (s : riscv_state) : «dfn'DIVU» (2,0,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 3 17 3) else «write'GPR» (BitVec.udiv (0 : BitVec 64) (3 : BitVec 64), 2) (fixture s 3 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (0 : BitVec 64) (3 : BitVec 64), 2) (fixture s 3 17 3) = _
 have numeric : (BitVec.udiv (0 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_12_7
example (s : riscv_state) : «dfn'DIVU» (7,0,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 3 17 3) else «write'GPR» (BitVec.udiv (0 : BitVec 64) (3 : BitVec 64), 7) (fixture s 3 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (0 : BitVec 64) (3 : BitVec 64), 7) (fixture s 3 17 3) = _
 have numeric : (BitVec.udiv (0 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_13_0
example (s : riscv_state) : «dfn'DIVU» (0,1,0) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; t) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 3 18446744073709551615 3) else «write'GPR» (BitVec.udiv (18446744073709551615 : BitVec 64) (0 : BitVec 64), 0) (fixture s 3 18446744073709551615 3)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 3 18446744073709551615 3) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_13_1
example (s : riscv_state) : «dfn'DIVU» (1,1,0) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 3 18446744073709551615 3) else «write'GPR» (BitVec.udiv (18446744073709551615 : BitVec 64) (0 : BitVec 64), 1) (fixture s 3 18446744073709551615 3)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 3 18446744073709551615 3) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_13_2
example (s : riscv_state) : «dfn'DIVU» (2,1,0) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 3 18446744073709551615 3) else «write'GPR» (BitVec.udiv (18446744073709551615 : BitVec 64) (0 : BitVec 64), 2) (fixture s 3 18446744073709551615 3)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 3 18446744073709551615 3) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_13_7
example (s : riscv_state) : «dfn'DIVU» (7,1,0) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 3 18446744073709551615 3) else «write'GPR» (BitVec.udiv (18446744073709551615 : BitVec 64) (0 : BitVec 64), 7) (fixture s 3 18446744073709551615 3)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 3 18446744073709551615 3) = _
 have numeric : (BitVec.signExtend 64 (BitVec.ofNat 1 1)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_14_0
example (s : riscv_state) : «dfn'DIVU» (0,1,1) (fixture s 3 9223372036854775808 2) = (let t := fixture s 3 9223372036854775808 2; t) := by
 change (if ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 0) (fixture s 3 9223372036854775808 2) else «write'GPR» (BitVec.udiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 0) (fixture s 3 9223372036854775808 2)) = _
 have divisorZero : ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 0) (fixture s 3 9223372036854775808 2) = _
 have numeric : (BitVec.udiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_14_1
example (s : riscv_state) : «dfn'DIVU» (1,1,1) (fixture s 3 9223372036854775808 2) = (let t := fixture s 3 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 1) (fixture s 3 9223372036854775808 2) else «write'GPR» (BitVec.udiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 1) (fixture s 3 9223372036854775808 2)) = _
 have divisorZero : ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 1) (fixture s 3 9223372036854775808 2) = _
 have numeric : (BitVec.udiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_14_2
example (s : riscv_state) : «dfn'DIVU» (2,1,1) (fixture s 3 9223372036854775808 2) = (let t := fixture s 3 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 2) (fixture s 3 9223372036854775808 2) else «write'GPR» (BitVec.udiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 2) (fixture s 3 9223372036854775808 2)) = _
 have divisorZero : ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 2) (fixture s 3 9223372036854775808 2) = _
 have numeric : (BitVec.udiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVU_3_14_7
example (s : riscv_state) : «dfn'DIVU» (7,1,1) (fixture s 3 9223372036854775808 2) = (let t := fixture s 3 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» (BitVec.signExtend 64 (BitVec.ofNat 1 1), 7) (fixture s 3 9223372036854775808 2) else «write'GPR» (BitVec.udiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 7) (fixture s 3 9223372036854775808 2)) = _
 have divisorZero : ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.udiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 7) (fixture s 3 9223372036854775808 2) = _
 have numeric : (BitVec.udiv (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_0_0
example (s : riscv_state) : «dfn'REMU» (0,1,2) (fixture s 0 0 0) = (let t := fixture s 0 0 0; t) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((0 : BitVec 64), 0) (fixture s 0 0 0) else «write'GPR» (BitVec.umod (0 : BitVec 64) (0 : BitVec 64), 0) (fixture s 0 0 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((0 : BitVec 64), 0) (fixture s 0 0 0) = _
 have numeric : ((0 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_0_1
example (s : riscv_state) : «dfn'REMU» (1,1,2) (fixture s 0 0 0) = (let t := fixture s 0 0 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((0 : BitVec 64), 1) (fixture s 0 0 0) else «write'GPR» (BitVec.umod (0 : BitVec 64) (0 : BitVec 64), 1) (fixture s 0 0 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((0 : BitVec 64), 1) (fixture s 0 0 0) = _
 have numeric : ((0 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_0_2
example (s : riscv_state) : «dfn'REMU» (2,1,2) (fixture s 0 0 0) = (let t := fixture s 0 0 0; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((0 : BitVec 64), 2) (fixture s 0 0 0) else «write'GPR» (BitVec.umod (0 : BitVec 64) (0 : BitVec 64), 2) (fixture s 0 0 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((0 : BitVec 64), 2) (fixture s 0 0 0) = _
 have numeric : ((0 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_0_7
example (s : riscv_state) : «dfn'REMU» (7,1,2) (fixture s 0 0 0) = (let t := fixture s 0 0 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((0 : BitVec 64), 7) (fixture s 0 0 0) else «write'GPR» (BitVec.umod (0 : BitVec 64) (0 : BitVec 64), 7) (fixture s 0 0 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((0 : BitVec 64), 7) (fixture s 0 0 0) = _
 have numeric : ((0 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_1_0
example (s : riscv_state) : «dfn'REMU» (0,1,2) (fixture s 0 17 0) = (let t := fixture s 0 17 0; t) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 0) (fixture s 0 17 0) else «write'GPR» (BitVec.umod (17 : BitVec 64) (0 : BitVec 64), 0) (fixture s 0 17 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((17 : BitVec 64), 0) (fixture s 0 17 0) = _
 have numeric : ((17 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_1_1
example (s : riscv_state) : «dfn'REMU» (1,1,2) (fixture s 0 17 0) = (let t := fixture s 0 17 0; {t with c_gpr := holUpdate 7 (holUpdate 1 17 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 1) (fixture s 0 17 0) else «write'GPR» (BitVec.umod (17 : BitVec 64) (0 : BitVec 64), 1) (fixture s 0 17 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((17 : BitVec 64), 1) (fixture s 0 17 0) = _
 have numeric : ((17 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_1_2
example (s : riscv_state) : «dfn'REMU» (2,1,2) (fixture s 0 17 0) = (let t := fixture s 0 17 0; {t with c_gpr := holUpdate 7 (holUpdate 2 17 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 2) (fixture s 0 17 0) else «write'GPR» (BitVec.umod (17 : BitVec 64) (0 : BitVec 64), 2) (fixture s 0 17 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((17 : BitVec 64), 2) (fixture s 0 17 0) = _
 have numeric : ((17 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_1_7
example (s : riscv_state) : «dfn'REMU» (7,1,2) (fixture s 0 17 0) = (let t := fixture s 0 17 0; {t with c_gpr := holUpdate 7 (holUpdate 7 17 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 7) (fixture s 0 17 0) else «write'GPR» (BitVec.umod (17 : BitVec 64) (0 : BitVec 64), 7) (fixture s 0 17 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((17 : BitVec 64), 7) (fixture s 0 17 0) = _
 have numeric : ((17 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_2_0
example (s : riscv_state) : «dfn'REMU» (0,1,2) (fixture s 0 18446744073709551615 0) = (let t := fixture s 0 18446744073709551615 0; t) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 0) (fixture s 0 18446744073709551615 0) else «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (0 : BitVec 64), 0) (fixture s 0 18446744073709551615 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((18446744073709551615 : BitVec 64), 0) (fixture s 0 18446744073709551615 0) = _
 have numeric : ((18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_2_1
example (s : riscv_state) : «dfn'REMU» (1,1,2) (fixture s 0 18446744073709551615 0) = (let t := fixture s 0 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 1) (fixture s 0 18446744073709551615 0) else «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (0 : BitVec 64), 1) (fixture s 0 18446744073709551615 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((18446744073709551615 : BitVec 64), 1) (fixture s 0 18446744073709551615 0) = _
 have numeric : ((18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_2_2
example (s : riscv_state) : «dfn'REMU» (2,1,2) (fixture s 0 18446744073709551615 0) = (let t := fixture s 0 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 2) (fixture s 0 18446744073709551615 0) else «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (0 : BitVec 64), 2) (fixture s 0 18446744073709551615 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((18446744073709551615 : BitVec 64), 2) (fixture s 0 18446744073709551615 0) = _
 have numeric : ((18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_2_7
example (s : riscv_state) : «dfn'REMU» (7,1,2) (fixture s 0 18446744073709551615 0) = (let t := fixture s 0 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 7) (fixture s 0 18446744073709551615 0) else «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (0 : BitVec 64), 7) (fixture s 0 18446744073709551615 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((18446744073709551615 : BitVec 64), 7) (fixture s 0 18446744073709551615 0) = _
 have numeric : ((18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_3_0
example (s : riscv_state) : «dfn'REMU» (0,1,2) (fixture s 0 17 3) = (let t := fixture s 0 17 3; t) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 0) (fixture s 0 17 3) else «write'GPR» (BitVec.umod (17 : BitVec 64) (3 : BitVec 64), 0) (fixture s 0 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (17 : BitVec 64) (3 : BitVec 64), 0) (fixture s 0 17 3) = _
 have numeric : (BitVec.umod (17 : BitVec 64) (3 : BitVec 64)) = (2 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_3_1
example (s : riscv_state) : «dfn'REMU» (1,1,2) (fixture s 0 17 3) = (let t := fixture s 0 17 3; {t with c_gpr := holUpdate 7 (holUpdate 1 2 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 1) (fixture s 0 17 3) else «write'GPR» (BitVec.umod (17 : BitVec 64) (3 : BitVec 64), 1) (fixture s 0 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (17 : BitVec 64) (3 : BitVec 64), 1) (fixture s 0 17 3) = _
 have numeric : (BitVec.umod (17 : BitVec 64) (3 : BitVec 64)) = (2 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_3_2
example (s : riscv_state) : «dfn'REMU» (2,1,2) (fixture s 0 17 3) = (let t := fixture s 0 17 3; {t with c_gpr := holUpdate 7 (holUpdate 2 2 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 2) (fixture s 0 17 3) else «write'GPR» (BitVec.umod (17 : BitVec 64) (3 : BitVec 64), 2) (fixture s 0 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (17 : BitVec 64) (3 : BitVec 64), 2) (fixture s 0 17 3) = _
 have numeric : (BitVec.umod (17 : BitVec 64) (3 : BitVec 64)) = (2 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_3_7
example (s : riscv_state) : «dfn'REMU» (7,1,2) (fixture s 0 17 3) = (let t := fixture s 0 17 3; {t with c_gpr := holUpdate 7 (holUpdate 7 2 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 7) (fixture s 0 17 3) else «write'GPR» (BitVec.umod (17 : BitVec 64) (3 : BitVec 64), 7) (fixture s 0 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (17 : BitVec 64) (3 : BitVec 64), 7) (fixture s 0 17 3) = _
 have numeric : (BitVec.umod (17 : BitVec 64) (3 : BitVec 64)) = (2 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_4_0
example (s : riscv_state) : «dfn'REMU» (0,1,2) (fixture s 0 18446744073709551599 3) = (let t := fixture s 0 18446744073709551599 3; t) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551599 : BitVec 64), 0) (fixture s 0 18446744073709551599 3) else «write'GPR» (BitVec.umod (18446744073709551599 : BitVec 64) (3 : BitVec 64), 0) (fixture s 0 18446744073709551599 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (18446744073709551599 : BitVec 64) (3 : BitVec 64), 0) (fixture s 0 18446744073709551599 3) = _
 have numeric : (BitVec.umod (18446744073709551599 : BitVec 64) (3 : BitVec 64)) = (2 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_4_1
example (s : riscv_state) : «dfn'REMU» (1,1,2) (fixture s 0 18446744073709551599 3) = (let t := fixture s 0 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 1 2 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551599 : BitVec 64), 1) (fixture s 0 18446744073709551599 3) else «write'GPR» (BitVec.umod (18446744073709551599 : BitVec 64) (3 : BitVec 64), 1) (fixture s 0 18446744073709551599 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (18446744073709551599 : BitVec 64) (3 : BitVec 64), 1) (fixture s 0 18446744073709551599 3) = _
 have numeric : (BitVec.umod (18446744073709551599 : BitVec 64) (3 : BitVec 64)) = (2 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_4_2
example (s : riscv_state) : «dfn'REMU» (2,1,2) (fixture s 0 18446744073709551599 3) = (let t := fixture s 0 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 2 2 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551599 : BitVec 64), 2) (fixture s 0 18446744073709551599 3) else «write'GPR» (BitVec.umod (18446744073709551599 : BitVec 64) (3 : BitVec 64), 2) (fixture s 0 18446744073709551599 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (18446744073709551599 : BitVec 64) (3 : BitVec 64), 2) (fixture s 0 18446744073709551599 3) = _
 have numeric : (BitVec.umod (18446744073709551599 : BitVec 64) (3 : BitVec 64)) = (2 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_4_7
example (s : riscv_state) : «dfn'REMU» (7,1,2) (fixture s 0 18446744073709551599 3) = (let t := fixture s 0 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 7 2 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551599 : BitVec 64), 7) (fixture s 0 18446744073709551599 3) else «write'GPR» (BitVec.umod (18446744073709551599 : BitVec 64) (3 : BitVec 64), 7) (fixture s 0 18446744073709551599 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (18446744073709551599 : BitVec 64) (3 : BitVec 64), 7) (fixture s 0 18446744073709551599 3) = _
 have numeric : (BitVec.umod (18446744073709551599 : BitVec 64) (3 : BitVec 64)) = (2 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_5_0
example (s : riscv_state) : «dfn'REMU» (0,1,2) (fixture s 0 17 18446744073709551613) = (let t := fixture s 0 17 18446744073709551613; t) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 0) (fixture s 0 17 18446744073709551613) else «write'GPR» (BitVec.umod (17 : BitVec 64) (18446744073709551613 : BitVec 64), 0) (fixture s 0 17 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (17 : BitVec 64) (18446744073709551613 : BitVec 64), 0) (fixture s 0 17 18446744073709551613) = _
 have numeric : (BitVec.umod (17 : BitVec 64) (18446744073709551613 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_5_1
example (s : riscv_state) : «dfn'REMU» (1,1,2) (fixture s 0 17 18446744073709551613) = (let t := fixture s 0 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 1 17 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 1) (fixture s 0 17 18446744073709551613) else «write'GPR» (BitVec.umod (17 : BitVec 64) (18446744073709551613 : BitVec 64), 1) (fixture s 0 17 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (17 : BitVec 64) (18446744073709551613 : BitVec 64), 1) (fixture s 0 17 18446744073709551613) = _
 have numeric : (BitVec.umod (17 : BitVec 64) (18446744073709551613 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_5_2
example (s : riscv_state) : «dfn'REMU» (2,1,2) (fixture s 0 17 18446744073709551613) = (let t := fixture s 0 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 2 17 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 2) (fixture s 0 17 18446744073709551613) else «write'GPR» (BitVec.umod (17 : BitVec 64) (18446744073709551613 : BitVec 64), 2) (fixture s 0 17 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (17 : BitVec 64) (18446744073709551613 : BitVec 64), 2) (fixture s 0 17 18446744073709551613) = _
 have numeric : (BitVec.umod (17 : BitVec 64) (18446744073709551613 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_5_7
example (s : riscv_state) : «dfn'REMU» (7,1,2) (fixture s 0 17 18446744073709551613) = (let t := fixture s 0 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 7 17 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 7) (fixture s 0 17 18446744073709551613) else «write'GPR» (BitVec.umod (17 : BitVec 64) (18446744073709551613 : BitVec 64), 7) (fixture s 0 17 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (17 : BitVec 64) (18446744073709551613 : BitVec 64), 7) (fixture s 0 17 18446744073709551613) = _
 have numeric : (BitVec.umod (17 : BitVec 64) (18446744073709551613 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_6_0
example (s : riscv_state) : «dfn'REMU» (0,1,2) (fixture s 0 18446744073709551599 18446744073709551613) = (let t := fixture s 0 18446744073709551599 18446744073709551613; t) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551599 : BitVec 64), 0) (fixture s 0 18446744073709551599 18446744073709551613) else «write'GPR» (BitVec.umod (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 0) (fixture s 0 18446744073709551599 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 0) (fixture s 0 18446744073709551599 18446744073709551613) = _
 have numeric : (BitVec.umod (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64)) = (18446744073709551599 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_6_1
example (s : riscv_state) : «dfn'REMU» (1,1,2) (fixture s 0 18446744073709551599 18446744073709551613) = (let t := fixture s 0 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551599 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551599 : BitVec 64), 1) (fixture s 0 18446744073709551599 18446744073709551613) else «write'GPR» (BitVec.umod (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 1) (fixture s 0 18446744073709551599 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 1) (fixture s 0 18446744073709551599 18446744073709551613) = _
 have numeric : (BitVec.umod (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64)) = (18446744073709551599 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_6_2
example (s : riscv_state) : «dfn'REMU» (2,1,2) (fixture s 0 18446744073709551599 18446744073709551613) = (let t := fixture s 0 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551599 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551599 : BitVec 64), 2) (fixture s 0 18446744073709551599 18446744073709551613) else «write'GPR» (BitVec.umod (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 2) (fixture s 0 18446744073709551599 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 2) (fixture s 0 18446744073709551599 18446744073709551613) = _
 have numeric : (BitVec.umod (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64)) = (18446744073709551599 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_6_7
example (s : riscv_state) : «dfn'REMU» (7,1,2) (fixture s 0 18446744073709551599 18446744073709551613) = (let t := fixture s 0 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551599 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551599 : BitVec 64), 7) (fixture s 0 18446744073709551599 18446744073709551613) else «write'GPR» (BitVec.umod (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 7) (fixture s 0 18446744073709551599 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 7) (fixture s 0 18446744073709551599 18446744073709551613) = _
 have numeric : (BitVec.umod (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64)) = (18446744073709551599 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_7_0
example (s : riscv_state) : «dfn'REMU» (0,1,2) (fixture s 0 9223372036854775808 18446744073709551615) = (let t := fixture s 0 9223372036854775808 18446744073709551615; t) := by
 change (if ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((9223372036854775808 : BitVec 64), 0) (fixture s 0 9223372036854775808 18446744073709551615) else «write'GPR» (BitVec.umod (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 0) (fixture s 0 9223372036854775808 18446744073709551615)) = _
 have divisorZero : ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 0) (fixture s 0 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.umod (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64)) = (9223372036854775808 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_7_1
example (s : riscv_state) : «dfn'REMU» (1,1,2) (fixture s 0 9223372036854775808 18446744073709551615) = (let t := fixture s 0 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((9223372036854775808 : BitVec 64), 1) (fixture s 0 9223372036854775808 18446744073709551615) else «write'GPR» (BitVec.umod (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 1) (fixture s 0 9223372036854775808 18446744073709551615)) = _
 have divisorZero : ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 1) (fixture s 0 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.umod (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64)) = (9223372036854775808 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_7_2
example (s : riscv_state) : «dfn'REMU» (2,1,2) (fixture s 0 9223372036854775808 18446744073709551615) = (let t := fixture s 0 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((9223372036854775808 : BitVec 64), 2) (fixture s 0 9223372036854775808 18446744073709551615) else «write'GPR» (BitVec.umod (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 2) (fixture s 0 9223372036854775808 18446744073709551615)) = _
 have divisorZero : ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 2) (fixture s 0 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.umod (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64)) = (9223372036854775808 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_7_7
example (s : riscv_state) : «dfn'REMU» (7,1,2) (fixture s 0 9223372036854775808 18446744073709551615) = (let t := fixture s 0 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((9223372036854775808 : BitVec 64), 7) (fixture s 0 9223372036854775808 18446744073709551615) else «write'GPR» (BitVec.umod (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 7) (fixture s 0 9223372036854775808 18446744073709551615)) = _
 have divisorZero : ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 7) (fixture s 0 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.umod (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64)) = (9223372036854775808 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_8_0
example (s : riscv_state) : «dfn'REMU» (0,1,2) (fixture s 0 2147483648 4294967295) = (let t := fixture s 0 2147483648 4294967295; t) := by
 change (if ((4294967295 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((2147483648 : BitVec 64), 0) (fixture s 0 2147483648 4294967295) else «write'GPR» (BitVec.umod (2147483648 : BitVec 64) (4294967295 : BitVec 64), 0) (fixture s 0 2147483648 4294967295)) = _
 have divisorZero : ((4294967295 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (2147483648 : BitVec 64) (4294967295 : BitVec 64), 0) (fixture s 0 2147483648 4294967295) = _
 have numeric : (BitVec.umod (2147483648 : BitVec 64) (4294967295 : BitVec 64)) = (2147483648 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_8_1
example (s : riscv_state) : «dfn'REMU» (1,1,2) (fixture s 0 2147483648 4294967295) = (let t := fixture s 0 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 1 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967295 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((2147483648 : BitVec 64), 1) (fixture s 0 2147483648 4294967295) else «write'GPR» (BitVec.umod (2147483648 : BitVec 64) (4294967295 : BitVec 64), 1) (fixture s 0 2147483648 4294967295)) = _
 have divisorZero : ((4294967295 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (2147483648 : BitVec 64) (4294967295 : BitVec 64), 1) (fixture s 0 2147483648 4294967295) = _
 have numeric : (BitVec.umod (2147483648 : BitVec 64) (4294967295 : BitVec 64)) = (2147483648 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_8_2
example (s : riscv_state) : «dfn'REMU» (2,1,2) (fixture s 0 2147483648 4294967295) = (let t := fixture s 0 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 2 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967295 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((2147483648 : BitVec 64), 2) (fixture s 0 2147483648 4294967295) else «write'GPR» (BitVec.umod (2147483648 : BitVec 64) (4294967295 : BitVec 64), 2) (fixture s 0 2147483648 4294967295)) = _
 have divisorZero : ((4294967295 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (2147483648 : BitVec 64) (4294967295 : BitVec 64), 2) (fixture s 0 2147483648 4294967295) = _
 have numeric : (BitVec.umod (2147483648 : BitVec 64) (4294967295 : BitVec 64)) = (2147483648 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_8_7
example (s : riscv_state) : «dfn'REMU» (7,1,2) (fixture s 0 2147483648 4294967295) = (let t := fixture s 0 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 7 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967295 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((2147483648 : BitVec 64), 7) (fixture s 0 2147483648 4294967295) else «write'GPR» (BitVec.umod (2147483648 : BitVec 64) (4294967295 : BitVec 64), 7) (fixture s 0 2147483648 4294967295)) = _
 have divisorZero : ((4294967295 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (2147483648 : BitVec 64) (4294967295 : BitVec 64), 7) (fixture s 0 2147483648 4294967295) = _
 have numeric : (BitVec.umod (2147483648 : BitVec 64) (4294967295 : BitVec 64)) = (2147483648 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_9_0
example (s : riscv_state) : «dfn'REMU» (0,1,2) (fixture s 0 4294967313 4294967296) = (let t := fixture s 0 4294967313 4294967296; t) := by
 change (if ((4294967296 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((4294967313 : BitVec 64), 0) (fixture s 0 4294967313 4294967296) else «write'GPR» (BitVec.umod (4294967313 : BitVec 64) (4294967296 : BitVec 64), 0) (fixture s 0 4294967313 4294967296)) = _
 have divisorZero : ((4294967296 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (4294967313 : BitVec 64) (4294967296 : BitVec 64), 0) (fixture s 0 4294967313 4294967296) = _
 have numeric : (BitVec.umod (4294967313 : BitVec 64) (4294967296 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_9_1
example (s : riscv_state) : «dfn'REMU» (1,1,2) (fixture s 0 4294967313 4294967296) = (let t := fixture s 0 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 1 17 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967296 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((4294967313 : BitVec 64), 1) (fixture s 0 4294967313 4294967296) else «write'GPR» (BitVec.umod (4294967313 : BitVec 64) (4294967296 : BitVec 64), 1) (fixture s 0 4294967313 4294967296)) = _
 have divisorZero : ((4294967296 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (4294967313 : BitVec 64) (4294967296 : BitVec 64), 1) (fixture s 0 4294967313 4294967296) = _
 have numeric : (BitVec.umod (4294967313 : BitVec 64) (4294967296 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_9_2
example (s : riscv_state) : «dfn'REMU» (2,1,2) (fixture s 0 4294967313 4294967296) = (let t := fixture s 0 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 2 17 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967296 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((4294967313 : BitVec 64), 2) (fixture s 0 4294967313 4294967296) else «write'GPR» (BitVec.umod (4294967313 : BitVec 64) (4294967296 : BitVec 64), 2) (fixture s 0 4294967313 4294967296)) = _
 have divisorZero : ((4294967296 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (4294967313 : BitVec 64) (4294967296 : BitVec 64), 2) (fixture s 0 4294967313 4294967296) = _
 have numeric : (BitVec.umod (4294967313 : BitVec 64) (4294967296 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_9_7
example (s : riscv_state) : «dfn'REMU» (7,1,2) (fixture s 0 4294967313 4294967296) = (let t := fixture s 0 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 7 17 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967296 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((4294967313 : BitVec 64), 7) (fixture s 0 4294967313 4294967296) else «write'GPR» (BitVec.umod (4294967313 : BitVec 64) (4294967296 : BitVec 64), 7) (fixture s 0 4294967313 4294967296)) = _
 have divisorZero : ((4294967296 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (4294967313 : BitVec 64) (4294967296 : BitVec 64), 7) (fixture s 0 4294967313 4294967296) = _
 have numeric : (BitVec.umod (4294967313 : BitVec 64) (4294967296 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_10_0
example (s : riscv_state) : «dfn'REMU» (0,1,2) (fixture s 0 18446744073709551615 2) = (let t := fixture s 0 18446744073709551615 2; t) := by
 change (if ((2 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 0) (fixture s 0 18446744073709551615 2) else «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (2 : BitVec 64), 0) (fixture s 0 18446744073709551615 2)) = _
 have divisorZero : ((2 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (2 : BitVec 64), 0) (fixture s 0 18446744073709551615 2) = _
 have numeric : (BitVec.umod (18446744073709551615 : BitVec 64) (2 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_10_1
example (s : riscv_state) : «dfn'REMU» (1,1,2) (fixture s 0 18446744073709551615 2) = (let t := fixture s 0 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((2 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 1) (fixture s 0 18446744073709551615 2) else «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (2 : BitVec 64), 1) (fixture s 0 18446744073709551615 2)) = _
 have divisorZero : ((2 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (2 : BitVec 64), 1) (fixture s 0 18446744073709551615 2) = _
 have numeric : (BitVec.umod (18446744073709551615 : BitVec 64) (2 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_10_2
example (s : riscv_state) : «dfn'REMU» (2,1,2) (fixture s 0 18446744073709551615 2) = (let t := fixture s 0 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((2 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 2) (fixture s 0 18446744073709551615 2) else «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (2 : BitVec 64), 2) (fixture s 0 18446744073709551615 2)) = _
 have divisorZero : ((2 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (2 : BitVec 64), 2) (fixture s 0 18446744073709551615 2) = _
 have numeric : (BitVec.umod (18446744073709551615 : BitVec 64) (2 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_10_7
example (s : riscv_state) : «dfn'REMU» (7,1,2) (fixture s 0 18446744073709551615 2) = (let t := fixture s 0 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((2 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 7) (fixture s 0 18446744073709551615 2) else «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (2 : BitVec 64), 7) (fixture s 0 18446744073709551615 2)) = _
 have divisorZero : ((2 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (2 : BitVec 64), 7) (fixture s 0 18446744073709551615 2) = _
 have numeric : (BitVec.umod (18446744073709551615 : BitVec 64) (2 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_11_0
example (s : riscv_state) : «dfn'REMU» (0,1,2) (fixture s 0 18446744073709551615 3) = (let t := fixture s 0 18446744073709551615 3; t) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 0) (fixture s 0 18446744073709551615 3) else «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (3 : BitVec 64), 0) (fixture s 0 18446744073709551615 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (3 : BitVec 64), 0) (fixture s 0 18446744073709551615 3) = _
 have numeric : (BitVec.umod (18446744073709551615 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_11_1
example (s : riscv_state) : «dfn'REMU» (1,1,2) (fixture s 0 18446744073709551615 3) = (let t := fixture s 0 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 1) (fixture s 0 18446744073709551615 3) else «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (3 : BitVec 64), 1) (fixture s 0 18446744073709551615 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (3 : BitVec 64), 1) (fixture s 0 18446744073709551615 3) = _
 have numeric : (BitVec.umod (18446744073709551615 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_11_2
example (s : riscv_state) : «dfn'REMU» (2,1,2) (fixture s 0 18446744073709551615 3) = (let t := fixture s 0 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 2) (fixture s 0 18446744073709551615 3) else «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (3 : BitVec 64), 2) (fixture s 0 18446744073709551615 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (3 : BitVec 64), 2) (fixture s 0 18446744073709551615 3) = _
 have numeric : (BitVec.umod (18446744073709551615 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_11_7
example (s : riscv_state) : «dfn'REMU» (7,1,2) (fixture s 0 18446744073709551615 3) = (let t := fixture s 0 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 7) (fixture s 0 18446744073709551615 3) else «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (3 : BitVec 64), 7) (fixture s 0 18446744073709551615 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (3 : BitVec 64), 7) (fixture s 0 18446744073709551615 3) = _
 have numeric : (BitVec.umod (18446744073709551615 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_12_0
example (s : riscv_state) : «dfn'REMU» (0,0,2) (fixture s 0 17 3) = (let t := fixture s 0 17 3; t) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((0 : BitVec 64), 0) (fixture s 0 17 3) else «write'GPR» (BitVec.umod (0 : BitVec 64) (3 : BitVec 64), 0) (fixture s 0 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (0 : BitVec 64) (3 : BitVec 64), 0) (fixture s 0 17 3) = _
 have numeric : (BitVec.umod (0 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_12_1
example (s : riscv_state) : «dfn'REMU» (1,0,2) (fixture s 0 17 3) = (let t := fixture s 0 17 3; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((0 : BitVec 64), 1) (fixture s 0 17 3) else «write'GPR» (BitVec.umod (0 : BitVec 64) (3 : BitVec 64), 1) (fixture s 0 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (0 : BitVec 64) (3 : BitVec 64), 1) (fixture s 0 17 3) = _
 have numeric : (BitVec.umod (0 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_12_2
example (s : riscv_state) : «dfn'REMU» (2,0,2) (fixture s 0 17 3) = (let t := fixture s 0 17 3; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((0 : BitVec 64), 2) (fixture s 0 17 3) else «write'GPR» (BitVec.umod (0 : BitVec 64) (3 : BitVec 64), 2) (fixture s 0 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (0 : BitVec 64) (3 : BitVec 64), 2) (fixture s 0 17 3) = _
 have numeric : (BitVec.umod (0 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_12_7
example (s : riscv_state) : «dfn'REMU» (7,0,2) (fixture s 0 17 3) = (let t := fixture s 0 17 3; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((0 : BitVec 64), 7) (fixture s 0 17 3) else «write'GPR» (BitVec.umod (0 : BitVec 64) (3 : BitVec 64), 7) (fixture s 0 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (0 : BitVec 64) (3 : BitVec 64), 7) (fixture s 0 17 3) = _
 have numeric : (BitVec.umod (0 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_13_0
example (s : riscv_state) : «dfn'REMU» (0,1,0) (fixture s 0 18446744073709551615 3) = (let t := fixture s 0 18446744073709551615 3; t) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 0) (fixture s 0 18446744073709551615 3) else «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (0 : BitVec 64), 0) (fixture s 0 18446744073709551615 3)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((18446744073709551615 : BitVec 64), 0) (fixture s 0 18446744073709551615 3) = _
 have numeric : ((18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_13_1
example (s : riscv_state) : «dfn'REMU» (1,1,0) (fixture s 0 18446744073709551615 3) = (let t := fixture s 0 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 1) (fixture s 0 18446744073709551615 3) else «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (0 : BitVec 64), 1) (fixture s 0 18446744073709551615 3)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((18446744073709551615 : BitVec 64), 1) (fixture s 0 18446744073709551615 3) = _
 have numeric : ((18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_13_2
example (s : riscv_state) : «dfn'REMU» (2,1,0) (fixture s 0 18446744073709551615 3) = (let t := fixture s 0 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 2) (fixture s 0 18446744073709551615 3) else «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (0 : BitVec 64), 2) (fixture s 0 18446744073709551615 3)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((18446744073709551615 : BitVec 64), 2) (fixture s 0 18446744073709551615 3) = _
 have numeric : ((18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_13_7
example (s : riscv_state) : «dfn'REMU» (7,1,0) (fixture s 0 18446744073709551615 3) = (let t := fixture s 0 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 7) (fixture s 0 18446744073709551615 3) else «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (0 : BitVec 64), 7) (fixture s 0 18446744073709551615 3)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((18446744073709551615 : BitVec 64), 7) (fixture s 0 18446744073709551615 3) = _
 have numeric : ((18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_14_0
example (s : riscv_state) : «dfn'REMU» (0,1,1) (fixture s 0 9223372036854775808 2) = (let t := fixture s 0 9223372036854775808 2; t) := by
 change (if ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((9223372036854775808 : BitVec 64), 0) (fixture s 0 9223372036854775808 2) else «write'GPR» (BitVec.umod (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 0) (fixture s 0 9223372036854775808 2)) = _
 have divisorZero : ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 0) (fixture s 0 9223372036854775808 2) = _
 have numeric : (BitVec.umod (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_14_1
example (s : riscv_state) : «dfn'REMU» (1,1,1) (fixture s 0 9223372036854775808 2) = (let t := fixture s 0 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((9223372036854775808 : BitVec 64), 1) (fixture s 0 9223372036854775808 2) else «write'GPR» (BitVec.umod (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 1) (fixture s 0 9223372036854775808 2)) = _
 have divisorZero : ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 1) (fixture s 0 9223372036854775808 2) = _
 have numeric : (BitVec.umod (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_14_2
example (s : riscv_state) : «dfn'REMU» (2,1,1) (fixture s 0 9223372036854775808 2) = (let t := fixture s 0 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((9223372036854775808 : BitVec 64), 2) (fixture s 0 9223372036854775808 2) else «write'GPR» (BitVec.umod (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 2) (fixture s 0 9223372036854775808 2)) = _
 have divisorZero : ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 2) (fixture s 0 9223372036854775808 2) = _
 have numeric : (BitVec.umod (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_0_14_7
example (s : riscv_state) : «dfn'REMU» (7,1,1) (fixture s 0 9223372036854775808 2) = (let t := fixture s 0 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((9223372036854775808 : BitVec 64), 7) (fixture s 0 9223372036854775808 2) else «write'GPR» (BitVec.umod (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 7) (fixture s 0 9223372036854775808 2)) = _
 have divisorZero : ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 7) (fixture s 0 9223372036854775808 2) = _
 have numeric : (BitVec.umod (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_0_0
example (s : riscv_state) : «dfn'REMU» (0,1,2) (fixture s 2 0 0) = (let t := fixture s 2 0 0; t) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((0 : BitVec 64), 0) (fixture s 2 0 0) else «write'GPR» (BitVec.umod (0 : BitVec 64) (0 : BitVec 64), 0) (fixture s 2 0 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((0 : BitVec 64), 0) (fixture s 2 0 0) = _
 have numeric : ((0 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_0_1
example (s : riscv_state) : «dfn'REMU» (1,1,2) (fixture s 2 0 0) = (let t := fixture s 2 0 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((0 : BitVec 64), 1) (fixture s 2 0 0) else «write'GPR» (BitVec.umod (0 : BitVec 64) (0 : BitVec 64), 1) (fixture s 2 0 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((0 : BitVec 64), 1) (fixture s 2 0 0) = _
 have numeric : ((0 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_0_2
example (s : riscv_state) : «dfn'REMU» (2,1,2) (fixture s 2 0 0) = (let t := fixture s 2 0 0; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((0 : BitVec 64), 2) (fixture s 2 0 0) else «write'GPR» (BitVec.umod (0 : BitVec 64) (0 : BitVec 64), 2) (fixture s 2 0 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((0 : BitVec 64), 2) (fixture s 2 0 0) = _
 have numeric : ((0 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_0_7
example (s : riscv_state) : «dfn'REMU» (7,1,2) (fixture s 2 0 0) = (let t := fixture s 2 0 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((0 : BitVec 64), 7) (fixture s 2 0 0) else «write'GPR» (BitVec.umod (0 : BitVec 64) (0 : BitVec 64), 7) (fixture s 2 0 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((0 : BitVec 64), 7) (fixture s 2 0 0) = _
 have numeric : ((0 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_1_0
example (s : riscv_state) : «dfn'REMU» (0,1,2) (fixture s 2 17 0) = (let t := fixture s 2 17 0; t) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 0) (fixture s 2 17 0) else «write'GPR» (BitVec.umod (17 : BitVec 64) (0 : BitVec 64), 0) (fixture s 2 17 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((17 : BitVec 64), 0) (fixture s 2 17 0) = _
 have numeric : ((17 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_1_1
example (s : riscv_state) : «dfn'REMU» (1,1,2) (fixture s 2 17 0) = (let t := fixture s 2 17 0; {t with c_gpr := holUpdate 7 (holUpdate 1 17 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 1) (fixture s 2 17 0) else «write'GPR» (BitVec.umod (17 : BitVec 64) (0 : BitVec 64), 1) (fixture s 2 17 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((17 : BitVec 64), 1) (fixture s 2 17 0) = _
 have numeric : ((17 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_1_2
example (s : riscv_state) : «dfn'REMU» (2,1,2) (fixture s 2 17 0) = (let t := fixture s 2 17 0; {t with c_gpr := holUpdate 7 (holUpdate 2 17 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 2) (fixture s 2 17 0) else «write'GPR» (BitVec.umod (17 : BitVec 64) (0 : BitVec 64), 2) (fixture s 2 17 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((17 : BitVec 64), 2) (fixture s 2 17 0) = _
 have numeric : ((17 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_1_7
example (s : riscv_state) : «dfn'REMU» (7,1,2) (fixture s 2 17 0) = (let t := fixture s 2 17 0; {t with c_gpr := holUpdate 7 (holUpdate 7 17 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 7) (fixture s 2 17 0) else «write'GPR» (BitVec.umod (17 : BitVec 64) (0 : BitVec 64), 7) (fixture s 2 17 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((17 : BitVec 64), 7) (fixture s 2 17 0) = _
 have numeric : ((17 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_2_0
example (s : riscv_state) : «dfn'REMU» (0,1,2) (fixture s 2 18446744073709551615 0) = (let t := fixture s 2 18446744073709551615 0; t) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 0) (fixture s 2 18446744073709551615 0) else «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (0 : BitVec 64), 0) (fixture s 2 18446744073709551615 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((18446744073709551615 : BitVec 64), 0) (fixture s 2 18446744073709551615 0) = _
 have numeric : ((18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_2_1
example (s : riscv_state) : «dfn'REMU» (1,1,2) (fixture s 2 18446744073709551615 0) = (let t := fixture s 2 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 1) (fixture s 2 18446744073709551615 0) else «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (0 : BitVec 64), 1) (fixture s 2 18446744073709551615 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((18446744073709551615 : BitVec 64), 1) (fixture s 2 18446744073709551615 0) = _
 have numeric : ((18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_2_2
example (s : riscv_state) : «dfn'REMU» (2,1,2) (fixture s 2 18446744073709551615 0) = (let t := fixture s 2 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 2) (fixture s 2 18446744073709551615 0) else «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (0 : BitVec 64), 2) (fixture s 2 18446744073709551615 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((18446744073709551615 : BitVec 64), 2) (fixture s 2 18446744073709551615 0) = _
 have numeric : ((18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_2_7
example (s : riscv_state) : «dfn'REMU» (7,1,2) (fixture s 2 18446744073709551615 0) = (let t := fixture s 2 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 7) (fixture s 2 18446744073709551615 0) else «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (0 : BitVec 64), 7) (fixture s 2 18446744073709551615 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((18446744073709551615 : BitVec 64), 7) (fixture s 2 18446744073709551615 0) = _
 have numeric : ((18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_3_0
example (s : riscv_state) : «dfn'REMU» (0,1,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; t) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 0) (fixture s 2 17 3) else «write'GPR» (BitVec.umod (17 : BitVec 64) (3 : BitVec 64), 0) (fixture s 2 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (17 : BitVec 64) (3 : BitVec 64), 0) (fixture s 2 17 3) = _
 have numeric : (BitVec.umod (17 : BitVec 64) (3 : BitVec 64)) = (2 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_3_1
example (s : riscv_state) : «dfn'REMU» (1,1,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; {t with c_gpr := holUpdate 7 (holUpdate 1 2 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 1) (fixture s 2 17 3) else «write'GPR» (BitVec.umod (17 : BitVec 64) (3 : BitVec 64), 1) (fixture s 2 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (17 : BitVec 64) (3 : BitVec 64), 1) (fixture s 2 17 3) = _
 have numeric : (BitVec.umod (17 : BitVec 64) (3 : BitVec 64)) = (2 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_3_2
example (s : riscv_state) : «dfn'REMU» (2,1,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; {t with c_gpr := holUpdate 7 (holUpdate 2 2 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 2) (fixture s 2 17 3) else «write'GPR» (BitVec.umod (17 : BitVec 64) (3 : BitVec 64), 2) (fixture s 2 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (17 : BitVec 64) (3 : BitVec 64), 2) (fixture s 2 17 3) = _
 have numeric : (BitVec.umod (17 : BitVec 64) (3 : BitVec 64)) = (2 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_3_7
example (s : riscv_state) : «dfn'REMU» (7,1,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; {t with c_gpr := holUpdate 7 (holUpdate 7 2 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 7) (fixture s 2 17 3) else «write'GPR» (BitVec.umod (17 : BitVec 64) (3 : BitVec 64), 7) (fixture s 2 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (17 : BitVec 64) (3 : BitVec 64), 7) (fixture s 2 17 3) = _
 have numeric : (BitVec.umod (17 : BitVec 64) (3 : BitVec 64)) = (2 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_4_0
example (s : riscv_state) : «dfn'REMU» (0,1,2) (fixture s 2 18446744073709551599 3) = (let t := fixture s 2 18446744073709551599 3; t) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551599 : BitVec 64), 0) (fixture s 2 18446744073709551599 3) else «write'GPR» (BitVec.umod (18446744073709551599 : BitVec 64) (3 : BitVec 64), 0) (fixture s 2 18446744073709551599 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (18446744073709551599 : BitVec 64) (3 : BitVec 64), 0) (fixture s 2 18446744073709551599 3) = _
 have numeric : (BitVec.umod (18446744073709551599 : BitVec 64) (3 : BitVec 64)) = (2 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_4_1
example (s : riscv_state) : «dfn'REMU» (1,1,2) (fixture s 2 18446744073709551599 3) = (let t := fixture s 2 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 1 2 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551599 : BitVec 64), 1) (fixture s 2 18446744073709551599 3) else «write'GPR» (BitVec.umod (18446744073709551599 : BitVec 64) (3 : BitVec 64), 1) (fixture s 2 18446744073709551599 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (18446744073709551599 : BitVec 64) (3 : BitVec 64), 1) (fixture s 2 18446744073709551599 3) = _
 have numeric : (BitVec.umod (18446744073709551599 : BitVec 64) (3 : BitVec 64)) = (2 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_4_2
example (s : riscv_state) : «dfn'REMU» (2,1,2) (fixture s 2 18446744073709551599 3) = (let t := fixture s 2 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 2 2 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551599 : BitVec 64), 2) (fixture s 2 18446744073709551599 3) else «write'GPR» (BitVec.umod (18446744073709551599 : BitVec 64) (3 : BitVec 64), 2) (fixture s 2 18446744073709551599 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (18446744073709551599 : BitVec 64) (3 : BitVec 64), 2) (fixture s 2 18446744073709551599 3) = _
 have numeric : (BitVec.umod (18446744073709551599 : BitVec 64) (3 : BitVec 64)) = (2 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_4_7
example (s : riscv_state) : «dfn'REMU» (7,1,2) (fixture s 2 18446744073709551599 3) = (let t := fixture s 2 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 7 2 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551599 : BitVec 64), 7) (fixture s 2 18446744073709551599 3) else «write'GPR» (BitVec.umod (18446744073709551599 : BitVec 64) (3 : BitVec 64), 7) (fixture s 2 18446744073709551599 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (18446744073709551599 : BitVec 64) (3 : BitVec 64), 7) (fixture s 2 18446744073709551599 3) = _
 have numeric : (BitVec.umod (18446744073709551599 : BitVec 64) (3 : BitVec 64)) = (2 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_5_0
example (s : riscv_state) : «dfn'REMU» (0,1,2) (fixture s 2 17 18446744073709551613) = (let t := fixture s 2 17 18446744073709551613; t) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 0) (fixture s 2 17 18446744073709551613) else «write'GPR» (BitVec.umod (17 : BitVec 64) (18446744073709551613 : BitVec 64), 0) (fixture s 2 17 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (17 : BitVec 64) (18446744073709551613 : BitVec 64), 0) (fixture s 2 17 18446744073709551613) = _
 have numeric : (BitVec.umod (17 : BitVec 64) (18446744073709551613 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_5_1
example (s : riscv_state) : «dfn'REMU» (1,1,2) (fixture s 2 17 18446744073709551613) = (let t := fixture s 2 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 1 17 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 1) (fixture s 2 17 18446744073709551613) else «write'GPR» (BitVec.umod (17 : BitVec 64) (18446744073709551613 : BitVec 64), 1) (fixture s 2 17 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (17 : BitVec 64) (18446744073709551613 : BitVec 64), 1) (fixture s 2 17 18446744073709551613) = _
 have numeric : (BitVec.umod (17 : BitVec 64) (18446744073709551613 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_5_2
example (s : riscv_state) : «dfn'REMU» (2,1,2) (fixture s 2 17 18446744073709551613) = (let t := fixture s 2 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 2 17 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 2) (fixture s 2 17 18446744073709551613) else «write'GPR» (BitVec.umod (17 : BitVec 64) (18446744073709551613 : BitVec 64), 2) (fixture s 2 17 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (17 : BitVec 64) (18446744073709551613 : BitVec 64), 2) (fixture s 2 17 18446744073709551613) = _
 have numeric : (BitVec.umod (17 : BitVec 64) (18446744073709551613 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_5_7
example (s : riscv_state) : «dfn'REMU» (7,1,2) (fixture s 2 17 18446744073709551613) = (let t := fixture s 2 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 7 17 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 7) (fixture s 2 17 18446744073709551613) else «write'GPR» (BitVec.umod (17 : BitVec 64) (18446744073709551613 : BitVec 64), 7) (fixture s 2 17 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (17 : BitVec 64) (18446744073709551613 : BitVec 64), 7) (fixture s 2 17 18446744073709551613) = _
 have numeric : (BitVec.umod (17 : BitVec 64) (18446744073709551613 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_6_0
example (s : riscv_state) : «dfn'REMU» (0,1,2) (fixture s 2 18446744073709551599 18446744073709551613) = (let t := fixture s 2 18446744073709551599 18446744073709551613; t) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551599 : BitVec 64), 0) (fixture s 2 18446744073709551599 18446744073709551613) else «write'GPR» (BitVec.umod (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 0) (fixture s 2 18446744073709551599 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 0) (fixture s 2 18446744073709551599 18446744073709551613) = _
 have numeric : (BitVec.umod (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64)) = (18446744073709551599 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_6_1
example (s : riscv_state) : «dfn'REMU» (1,1,2) (fixture s 2 18446744073709551599 18446744073709551613) = (let t := fixture s 2 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551599 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551599 : BitVec 64), 1) (fixture s 2 18446744073709551599 18446744073709551613) else «write'GPR» (BitVec.umod (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 1) (fixture s 2 18446744073709551599 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 1) (fixture s 2 18446744073709551599 18446744073709551613) = _
 have numeric : (BitVec.umod (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64)) = (18446744073709551599 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_6_2
example (s : riscv_state) : «dfn'REMU» (2,1,2) (fixture s 2 18446744073709551599 18446744073709551613) = (let t := fixture s 2 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551599 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551599 : BitVec 64), 2) (fixture s 2 18446744073709551599 18446744073709551613) else «write'GPR» (BitVec.umod (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 2) (fixture s 2 18446744073709551599 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 2) (fixture s 2 18446744073709551599 18446744073709551613) = _
 have numeric : (BitVec.umod (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64)) = (18446744073709551599 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_6_7
example (s : riscv_state) : «dfn'REMU» (7,1,2) (fixture s 2 18446744073709551599 18446744073709551613) = (let t := fixture s 2 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551599 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551599 : BitVec 64), 7) (fixture s 2 18446744073709551599 18446744073709551613) else «write'GPR» (BitVec.umod (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 7) (fixture s 2 18446744073709551599 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 7) (fixture s 2 18446744073709551599 18446744073709551613) = _
 have numeric : (BitVec.umod (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64)) = (18446744073709551599 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_7_0
example (s : riscv_state) : «dfn'REMU» (0,1,2) (fixture s 2 9223372036854775808 18446744073709551615) = (let t := fixture s 2 9223372036854775808 18446744073709551615; t) := by
 change (if ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((9223372036854775808 : BitVec 64), 0) (fixture s 2 9223372036854775808 18446744073709551615) else «write'GPR» (BitVec.umod (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 0) (fixture s 2 9223372036854775808 18446744073709551615)) = _
 have divisorZero : ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 0) (fixture s 2 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.umod (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64)) = (9223372036854775808 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_7_1
example (s : riscv_state) : «dfn'REMU» (1,1,2) (fixture s 2 9223372036854775808 18446744073709551615) = (let t := fixture s 2 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((9223372036854775808 : BitVec 64), 1) (fixture s 2 9223372036854775808 18446744073709551615) else «write'GPR» (BitVec.umod (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 1) (fixture s 2 9223372036854775808 18446744073709551615)) = _
 have divisorZero : ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 1) (fixture s 2 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.umod (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64)) = (9223372036854775808 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_7_2
example (s : riscv_state) : «dfn'REMU» (2,1,2) (fixture s 2 9223372036854775808 18446744073709551615) = (let t := fixture s 2 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((9223372036854775808 : BitVec 64), 2) (fixture s 2 9223372036854775808 18446744073709551615) else «write'GPR» (BitVec.umod (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 2) (fixture s 2 9223372036854775808 18446744073709551615)) = _
 have divisorZero : ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 2) (fixture s 2 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.umod (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64)) = (9223372036854775808 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_7_7
example (s : riscv_state) : «dfn'REMU» (7,1,2) (fixture s 2 9223372036854775808 18446744073709551615) = (let t := fixture s 2 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((9223372036854775808 : BitVec 64), 7) (fixture s 2 9223372036854775808 18446744073709551615) else «write'GPR» (BitVec.umod (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 7) (fixture s 2 9223372036854775808 18446744073709551615)) = _
 have divisorZero : ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 7) (fixture s 2 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.umod (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64)) = (9223372036854775808 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_8_0
example (s : riscv_state) : «dfn'REMU» (0,1,2) (fixture s 2 2147483648 4294967295) = (let t := fixture s 2 2147483648 4294967295; t) := by
 change (if ((4294967295 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((2147483648 : BitVec 64), 0) (fixture s 2 2147483648 4294967295) else «write'GPR» (BitVec.umod (2147483648 : BitVec 64) (4294967295 : BitVec 64), 0) (fixture s 2 2147483648 4294967295)) = _
 have divisorZero : ((4294967295 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (2147483648 : BitVec 64) (4294967295 : BitVec 64), 0) (fixture s 2 2147483648 4294967295) = _
 have numeric : (BitVec.umod (2147483648 : BitVec 64) (4294967295 : BitVec 64)) = (2147483648 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_8_1
example (s : riscv_state) : «dfn'REMU» (1,1,2) (fixture s 2 2147483648 4294967295) = (let t := fixture s 2 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 1 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967295 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((2147483648 : BitVec 64), 1) (fixture s 2 2147483648 4294967295) else «write'GPR» (BitVec.umod (2147483648 : BitVec 64) (4294967295 : BitVec 64), 1) (fixture s 2 2147483648 4294967295)) = _
 have divisorZero : ((4294967295 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (2147483648 : BitVec 64) (4294967295 : BitVec 64), 1) (fixture s 2 2147483648 4294967295) = _
 have numeric : (BitVec.umod (2147483648 : BitVec 64) (4294967295 : BitVec 64)) = (2147483648 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_8_2
example (s : riscv_state) : «dfn'REMU» (2,1,2) (fixture s 2 2147483648 4294967295) = (let t := fixture s 2 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 2 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967295 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((2147483648 : BitVec 64), 2) (fixture s 2 2147483648 4294967295) else «write'GPR» (BitVec.umod (2147483648 : BitVec 64) (4294967295 : BitVec 64), 2) (fixture s 2 2147483648 4294967295)) = _
 have divisorZero : ((4294967295 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (2147483648 : BitVec 64) (4294967295 : BitVec 64), 2) (fixture s 2 2147483648 4294967295) = _
 have numeric : (BitVec.umod (2147483648 : BitVec 64) (4294967295 : BitVec 64)) = (2147483648 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_8_7
example (s : riscv_state) : «dfn'REMU» (7,1,2) (fixture s 2 2147483648 4294967295) = (let t := fixture s 2 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 7 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967295 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((2147483648 : BitVec 64), 7) (fixture s 2 2147483648 4294967295) else «write'GPR» (BitVec.umod (2147483648 : BitVec 64) (4294967295 : BitVec 64), 7) (fixture s 2 2147483648 4294967295)) = _
 have divisorZero : ((4294967295 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (2147483648 : BitVec 64) (4294967295 : BitVec 64), 7) (fixture s 2 2147483648 4294967295) = _
 have numeric : (BitVec.umod (2147483648 : BitVec 64) (4294967295 : BitVec 64)) = (2147483648 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_9_0
example (s : riscv_state) : «dfn'REMU» (0,1,2) (fixture s 2 4294967313 4294967296) = (let t := fixture s 2 4294967313 4294967296; t) := by
 change (if ((4294967296 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((4294967313 : BitVec 64), 0) (fixture s 2 4294967313 4294967296) else «write'GPR» (BitVec.umod (4294967313 : BitVec 64) (4294967296 : BitVec 64), 0) (fixture s 2 4294967313 4294967296)) = _
 have divisorZero : ((4294967296 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (4294967313 : BitVec 64) (4294967296 : BitVec 64), 0) (fixture s 2 4294967313 4294967296) = _
 have numeric : (BitVec.umod (4294967313 : BitVec 64) (4294967296 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_9_1
example (s : riscv_state) : «dfn'REMU» (1,1,2) (fixture s 2 4294967313 4294967296) = (let t := fixture s 2 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 1 17 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967296 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((4294967313 : BitVec 64), 1) (fixture s 2 4294967313 4294967296) else «write'GPR» (BitVec.umod (4294967313 : BitVec 64) (4294967296 : BitVec 64), 1) (fixture s 2 4294967313 4294967296)) = _
 have divisorZero : ((4294967296 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (4294967313 : BitVec 64) (4294967296 : BitVec 64), 1) (fixture s 2 4294967313 4294967296) = _
 have numeric : (BitVec.umod (4294967313 : BitVec 64) (4294967296 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_9_2
example (s : riscv_state) : «dfn'REMU» (2,1,2) (fixture s 2 4294967313 4294967296) = (let t := fixture s 2 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 2 17 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967296 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((4294967313 : BitVec 64), 2) (fixture s 2 4294967313 4294967296) else «write'GPR» (BitVec.umod (4294967313 : BitVec 64) (4294967296 : BitVec 64), 2) (fixture s 2 4294967313 4294967296)) = _
 have divisorZero : ((4294967296 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (4294967313 : BitVec 64) (4294967296 : BitVec 64), 2) (fixture s 2 4294967313 4294967296) = _
 have numeric : (BitVec.umod (4294967313 : BitVec 64) (4294967296 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_9_7
example (s : riscv_state) : «dfn'REMU» (7,1,2) (fixture s 2 4294967313 4294967296) = (let t := fixture s 2 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 7 17 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967296 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((4294967313 : BitVec 64), 7) (fixture s 2 4294967313 4294967296) else «write'GPR» (BitVec.umod (4294967313 : BitVec 64) (4294967296 : BitVec 64), 7) (fixture s 2 4294967313 4294967296)) = _
 have divisorZero : ((4294967296 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (4294967313 : BitVec 64) (4294967296 : BitVec 64), 7) (fixture s 2 4294967313 4294967296) = _
 have numeric : (BitVec.umod (4294967313 : BitVec 64) (4294967296 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_10_0
example (s : riscv_state) : «dfn'REMU» (0,1,2) (fixture s 2 18446744073709551615 2) = (let t := fixture s 2 18446744073709551615 2; t) := by
 change (if ((2 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 0) (fixture s 2 18446744073709551615 2) else «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (2 : BitVec 64), 0) (fixture s 2 18446744073709551615 2)) = _
 have divisorZero : ((2 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (2 : BitVec 64), 0) (fixture s 2 18446744073709551615 2) = _
 have numeric : (BitVec.umod (18446744073709551615 : BitVec 64) (2 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_10_1
example (s : riscv_state) : «dfn'REMU» (1,1,2) (fixture s 2 18446744073709551615 2) = (let t := fixture s 2 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((2 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 1) (fixture s 2 18446744073709551615 2) else «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (2 : BitVec 64), 1) (fixture s 2 18446744073709551615 2)) = _
 have divisorZero : ((2 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (2 : BitVec 64), 1) (fixture s 2 18446744073709551615 2) = _
 have numeric : (BitVec.umod (18446744073709551615 : BitVec 64) (2 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_10_2
example (s : riscv_state) : «dfn'REMU» (2,1,2) (fixture s 2 18446744073709551615 2) = (let t := fixture s 2 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((2 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 2) (fixture s 2 18446744073709551615 2) else «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (2 : BitVec 64), 2) (fixture s 2 18446744073709551615 2)) = _
 have divisorZero : ((2 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (2 : BitVec 64), 2) (fixture s 2 18446744073709551615 2) = _
 have numeric : (BitVec.umod (18446744073709551615 : BitVec 64) (2 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_10_7
example (s : riscv_state) : «dfn'REMU» (7,1,2) (fixture s 2 18446744073709551615 2) = (let t := fixture s 2 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((2 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 7) (fixture s 2 18446744073709551615 2) else «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (2 : BitVec 64), 7) (fixture s 2 18446744073709551615 2)) = _
 have divisorZero : ((2 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (2 : BitVec 64), 7) (fixture s 2 18446744073709551615 2) = _
 have numeric : (BitVec.umod (18446744073709551615 : BitVec 64) (2 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_11_0
example (s : riscv_state) : «dfn'REMU» (0,1,2) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; t) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 0) (fixture s 2 18446744073709551615 3) else «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (3 : BitVec 64), 0) (fixture s 2 18446744073709551615 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (3 : BitVec 64), 0) (fixture s 2 18446744073709551615 3) = _
 have numeric : (BitVec.umod (18446744073709551615 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_11_1
example (s : riscv_state) : «dfn'REMU» (1,1,2) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 1) (fixture s 2 18446744073709551615 3) else «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (3 : BitVec 64), 1) (fixture s 2 18446744073709551615 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (3 : BitVec 64), 1) (fixture s 2 18446744073709551615 3) = _
 have numeric : (BitVec.umod (18446744073709551615 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_11_2
example (s : riscv_state) : «dfn'REMU» (2,1,2) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 2) (fixture s 2 18446744073709551615 3) else «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (3 : BitVec 64), 2) (fixture s 2 18446744073709551615 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (3 : BitVec 64), 2) (fixture s 2 18446744073709551615 3) = _
 have numeric : (BitVec.umod (18446744073709551615 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_11_7
example (s : riscv_state) : «dfn'REMU» (7,1,2) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 7) (fixture s 2 18446744073709551615 3) else «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (3 : BitVec 64), 7) (fixture s 2 18446744073709551615 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (3 : BitVec 64), 7) (fixture s 2 18446744073709551615 3) = _
 have numeric : (BitVec.umod (18446744073709551615 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_12_0
example (s : riscv_state) : «dfn'REMU» (0,0,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; t) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((0 : BitVec 64), 0) (fixture s 2 17 3) else «write'GPR» (BitVec.umod (0 : BitVec 64) (3 : BitVec 64), 0) (fixture s 2 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (0 : BitVec 64) (3 : BitVec 64), 0) (fixture s 2 17 3) = _
 have numeric : (BitVec.umod (0 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_12_1
example (s : riscv_state) : «dfn'REMU» (1,0,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((0 : BitVec 64), 1) (fixture s 2 17 3) else «write'GPR» (BitVec.umod (0 : BitVec 64) (3 : BitVec 64), 1) (fixture s 2 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (0 : BitVec 64) (3 : BitVec 64), 1) (fixture s 2 17 3) = _
 have numeric : (BitVec.umod (0 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_12_2
example (s : riscv_state) : «dfn'REMU» (2,0,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((0 : BitVec 64), 2) (fixture s 2 17 3) else «write'GPR» (BitVec.umod (0 : BitVec 64) (3 : BitVec 64), 2) (fixture s 2 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (0 : BitVec 64) (3 : BitVec 64), 2) (fixture s 2 17 3) = _
 have numeric : (BitVec.umod (0 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_12_7
example (s : riscv_state) : «dfn'REMU» (7,0,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((0 : BitVec 64), 7) (fixture s 2 17 3) else «write'GPR» (BitVec.umod (0 : BitVec 64) (3 : BitVec 64), 7) (fixture s 2 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (0 : BitVec 64) (3 : BitVec 64), 7) (fixture s 2 17 3) = _
 have numeric : (BitVec.umod (0 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_13_0
example (s : riscv_state) : «dfn'REMU» (0,1,0) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; t) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 0) (fixture s 2 18446744073709551615 3) else «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (0 : BitVec 64), 0) (fixture s 2 18446744073709551615 3)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((18446744073709551615 : BitVec 64), 0) (fixture s 2 18446744073709551615 3) = _
 have numeric : ((18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_13_1
example (s : riscv_state) : «dfn'REMU» (1,1,0) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 1) (fixture s 2 18446744073709551615 3) else «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (0 : BitVec 64), 1) (fixture s 2 18446744073709551615 3)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((18446744073709551615 : BitVec 64), 1) (fixture s 2 18446744073709551615 3) = _
 have numeric : ((18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_13_2
example (s : riscv_state) : «dfn'REMU» (2,1,0) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 2) (fixture s 2 18446744073709551615 3) else «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (0 : BitVec 64), 2) (fixture s 2 18446744073709551615 3)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((18446744073709551615 : BitVec 64), 2) (fixture s 2 18446744073709551615 3) = _
 have numeric : ((18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_13_7
example (s : riscv_state) : «dfn'REMU» (7,1,0) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 7) (fixture s 2 18446744073709551615 3) else «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (0 : BitVec 64), 7) (fixture s 2 18446744073709551615 3)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((18446744073709551615 : BitVec 64), 7) (fixture s 2 18446744073709551615 3) = _
 have numeric : ((18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_14_0
example (s : riscv_state) : «dfn'REMU» (0,1,1) (fixture s 2 9223372036854775808 2) = (let t := fixture s 2 9223372036854775808 2; t) := by
 change (if ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((9223372036854775808 : BitVec 64), 0) (fixture s 2 9223372036854775808 2) else «write'GPR» (BitVec.umod (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 0) (fixture s 2 9223372036854775808 2)) = _
 have divisorZero : ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 0) (fixture s 2 9223372036854775808 2) = _
 have numeric : (BitVec.umod (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_14_1
example (s : riscv_state) : «dfn'REMU» (1,1,1) (fixture s 2 9223372036854775808 2) = (let t := fixture s 2 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((9223372036854775808 : BitVec 64), 1) (fixture s 2 9223372036854775808 2) else «write'GPR» (BitVec.umod (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 1) (fixture s 2 9223372036854775808 2)) = _
 have divisorZero : ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 1) (fixture s 2 9223372036854775808 2) = _
 have numeric : (BitVec.umod (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_14_2
example (s : riscv_state) : «dfn'REMU» (2,1,1) (fixture s 2 9223372036854775808 2) = (let t := fixture s 2 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((9223372036854775808 : BitVec 64), 2) (fixture s 2 9223372036854775808 2) else «write'GPR» (BitVec.umod (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 2) (fixture s 2 9223372036854775808 2)) = _
 have divisorZero : ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 2) (fixture s 2 9223372036854775808 2) = _
 have numeric : (BitVec.umod (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_2_14_7
example (s : riscv_state) : «dfn'REMU» (7,1,1) (fixture s 2 9223372036854775808 2) = (let t := fixture s 2 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((9223372036854775808 : BitVec 64), 7) (fixture s 2 9223372036854775808 2) else «write'GPR» (BitVec.umod (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 7) (fixture s 2 9223372036854775808 2)) = _
 have divisorZero : ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 7) (fixture s 2 9223372036854775808 2) = _
 have numeric : (BitVec.umod (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_0_0
example (s : riscv_state) : «dfn'REMU» (0,1,2) (fixture s 3 0 0) = (let t := fixture s 3 0 0; t) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((0 : BitVec 64), 0) (fixture s 3 0 0) else «write'GPR» (BitVec.umod (0 : BitVec 64) (0 : BitVec 64), 0) (fixture s 3 0 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((0 : BitVec 64), 0) (fixture s 3 0 0) = _
 have numeric : ((0 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_0_1
example (s : riscv_state) : «dfn'REMU» (1,1,2) (fixture s 3 0 0) = (let t := fixture s 3 0 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((0 : BitVec 64), 1) (fixture s 3 0 0) else «write'GPR» (BitVec.umod (0 : BitVec 64) (0 : BitVec 64), 1) (fixture s 3 0 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((0 : BitVec 64), 1) (fixture s 3 0 0) = _
 have numeric : ((0 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_0_2
example (s : riscv_state) : «dfn'REMU» (2,1,2) (fixture s 3 0 0) = (let t := fixture s 3 0 0; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((0 : BitVec 64), 2) (fixture s 3 0 0) else «write'GPR» (BitVec.umod (0 : BitVec 64) (0 : BitVec 64), 2) (fixture s 3 0 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((0 : BitVec 64), 2) (fixture s 3 0 0) = _
 have numeric : ((0 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_0_7
example (s : riscv_state) : «dfn'REMU» (7,1,2) (fixture s 3 0 0) = (let t := fixture s 3 0 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((0 : BitVec 64), 7) (fixture s 3 0 0) else «write'GPR» (BitVec.umod (0 : BitVec 64) (0 : BitVec 64), 7) (fixture s 3 0 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((0 : BitVec 64), 7) (fixture s 3 0 0) = _
 have numeric : ((0 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_1_0
example (s : riscv_state) : «dfn'REMU» (0,1,2) (fixture s 3 17 0) = (let t := fixture s 3 17 0; t) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 0) (fixture s 3 17 0) else «write'GPR» (BitVec.umod (17 : BitVec 64) (0 : BitVec 64), 0) (fixture s 3 17 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((17 : BitVec 64), 0) (fixture s 3 17 0) = _
 have numeric : ((17 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_1_1
example (s : riscv_state) : «dfn'REMU» (1,1,2) (fixture s 3 17 0) = (let t := fixture s 3 17 0; {t with c_gpr := holUpdate 7 (holUpdate 1 17 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 1) (fixture s 3 17 0) else «write'GPR» (BitVec.umod (17 : BitVec 64) (0 : BitVec 64), 1) (fixture s 3 17 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((17 : BitVec 64), 1) (fixture s 3 17 0) = _
 have numeric : ((17 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_1_2
example (s : riscv_state) : «dfn'REMU» (2,1,2) (fixture s 3 17 0) = (let t := fixture s 3 17 0; {t with c_gpr := holUpdate 7 (holUpdate 2 17 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 2) (fixture s 3 17 0) else «write'GPR» (BitVec.umod (17 : BitVec 64) (0 : BitVec 64), 2) (fixture s 3 17 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((17 : BitVec 64), 2) (fixture s 3 17 0) = _
 have numeric : ((17 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_1_7
example (s : riscv_state) : «dfn'REMU» (7,1,2) (fixture s 3 17 0) = (let t := fixture s 3 17 0; {t with c_gpr := holUpdate 7 (holUpdate 7 17 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 7) (fixture s 3 17 0) else «write'GPR» (BitVec.umod (17 : BitVec 64) (0 : BitVec 64), 7) (fixture s 3 17 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((17 : BitVec 64), 7) (fixture s 3 17 0) = _
 have numeric : ((17 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_2_0
example (s : riscv_state) : «dfn'REMU» (0,1,2) (fixture s 3 18446744073709551615 0) = (let t := fixture s 3 18446744073709551615 0; t) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 0) (fixture s 3 18446744073709551615 0) else «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (0 : BitVec 64), 0) (fixture s 3 18446744073709551615 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((18446744073709551615 : BitVec 64), 0) (fixture s 3 18446744073709551615 0) = _
 have numeric : ((18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_2_1
example (s : riscv_state) : «dfn'REMU» (1,1,2) (fixture s 3 18446744073709551615 0) = (let t := fixture s 3 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 1) (fixture s 3 18446744073709551615 0) else «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (0 : BitVec 64), 1) (fixture s 3 18446744073709551615 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((18446744073709551615 : BitVec 64), 1) (fixture s 3 18446744073709551615 0) = _
 have numeric : ((18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_2_2
example (s : riscv_state) : «dfn'REMU» (2,1,2) (fixture s 3 18446744073709551615 0) = (let t := fixture s 3 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 2) (fixture s 3 18446744073709551615 0) else «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (0 : BitVec 64), 2) (fixture s 3 18446744073709551615 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((18446744073709551615 : BitVec 64), 2) (fixture s 3 18446744073709551615 0) = _
 have numeric : ((18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_2_7
example (s : riscv_state) : «dfn'REMU» (7,1,2) (fixture s 3 18446744073709551615 0) = (let t := fixture s 3 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 7) (fixture s 3 18446744073709551615 0) else «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (0 : BitVec 64), 7) (fixture s 3 18446744073709551615 0)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((18446744073709551615 : BitVec 64), 7) (fixture s 3 18446744073709551615 0) = _
 have numeric : ((18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_3_0
example (s : riscv_state) : «dfn'REMU» (0,1,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; t) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 0) (fixture s 3 17 3) else «write'GPR» (BitVec.umod (17 : BitVec 64) (3 : BitVec 64), 0) (fixture s 3 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (17 : BitVec 64) (3 : BitVec 64), 0) (fixture s 3 17 3) = _
 have numeric : (BitVec.umod (17 : BitVec 64) (3 : BitVec 64)) = (2 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_3_1
example (s : riscv_state) : «dfn'REMU» (1,1,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; {t with c_gpr := holUpdate 7 (holUpdate 1 2 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 1) (fixture s 3 17 3) else «write'GPR» (BitVec.umod (17 : BitVec 64) (3 : BitVec 64), 1) (fixture s 3 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (17 : BitVec 64) (3 : BitVec 64), 1) (fixture s 3 17 3) = _
 have numeric : (BitVec.umod (17 : BitVec 64) (3 : BitVec 64)) = (2 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_3_2
example (s : riscv_state) : «dfn'REMU» (2,1,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; {t with c_gpr := holUpdate 7 (holUpdate 2 2 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 2) (fixture s 3 17 3) else «write'GPR» (BitVec.umod (17 : BitVec 64) (3 : BitVec 64), 2) (fixture s 3 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (17 : BitVec 64) (3 : BitVec 64), 2) (fixture s 3 17 3) = _
 have numeric : (BitVec.umod (17 : BitVec 64) (3 : BitVec 64)) = (2 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_3_7
example (s : riscv_state) : «dfn'REMU» (7,1,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; {t with c_gpr := holUpdate 7 (holUpdate 7 2 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 7) (fixture s 3 17 3) else «write'GPR» (BitVec.umod (17 : BitVec 64) (3 : BitVec 64), 7) (fixture s 3 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (17 : BitVec 64) (3 : BitVec 64), 7) (fixture s 3 17 3) = _
 have numeric : (BitVec.umod (17 : BitVec 64) (3 : BitVec 64)) = (2 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_4_0
example (s : riscv_state) : «dfn'REMU» (0,1,2) (fixture s 3 18446744073709551599 3) = (let t := fixture s 3 18446744073709551599 3; t) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551599 : BitVec 64), 0) (fixture s 3 18446744073709551599 3) else «write'GPR» (BitVec.umod (18446744073709551599 : BitVec 64) (3 : BitVec 64), 0) (fixture s 3 18446744073709551599 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (18446744073709551599 : BitVec 64) (3 : BitVec 64), 0) (fixture s 3 18446744073709551599 3) = _
 have numeric : (BitVec.umod (18446744073709551599 : BitVec 64) (3 : BitVec 64)) = (2 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_4_1
example (s : riscv_state) : «dfn'REMU» (1,1,2) (fixture s 3 18446744073709551599 3) = (let t := fixture s 3 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 1 2 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551599 : BitVec 64), 1) (fixture s 3 18446744073709551599 3) else «write'GPR» (BitVec.umod (18446744073709551599 : BitVec 64) (3 : BitVec 64), 1) (fixture s 3 18446744073709551599 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (18446744073709551599 : BitVec 64) (3 : BitVec 64), 1) (fixture s 3 18446744073709551599 3) = _
 have numeric : (BitVec.umod (18446744073709551599 : BitVec 64) (3 : BitVec 64)) = (2 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_4_2
example (s : riscv_state) : «dfn'REMU» (2,1,2) (fixture s 3 18446744073709551599 3) = (let t := fixture s 3 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 2 2 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551599 : BitVec 64), 2) (fixture s 3 18446744073709551599 3) else «write'GPR» (BitVec.umod (18446744073709551599 : BitVec 64) (3 : BitVec 64), 2) (fixture s 3 18446744073709551599 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (18446744073709551599 : BitVec 64) (3 : BitVec 64), 2) (fixture s 3 18446744073709551599 3) = _
 have numeric : (BitVec.umod (18446744073709551599 : BitVec 64) (3 : BitVec 64)) = (2 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_4_7
example (s : riscv_state) : «dfn'REMU» (7,1,2) (fixture s 3 18446744073709551599 3) = (let t := fixture s 3 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 7 2 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551599 : BitVec 64), 7) (fixture s 3 18446744073709551599 3) else «write'GPR» (BitVec.umod (18446744073709551599 : BitVec 64) (3 : BitVec 64), 7) (fixture s 3 18446744073709551599 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (18446744073709551599 : BitVec 64) (3 : BitVec 64), 7) (fixture s 3 18446744073709551599 3) = _
 have numeric : (BitVec.umod (18446744073709551599 : BitVec 64) (3 : BitVec 64)) = (2 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_5_0
example (s : riscv_state) : «dfn'REMU» (0,1,2) (fixture s 3 17 18446744073709551613) = (let t := fixture s 3 17 18446744073709551613; t) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 0) (fixture s 3 17 18446744073709551613) else «write'GPR» (BitVec.umod (17 : BitVec 64) (18446744073709551613 : BitVec 64), 0) (fixture s 3 17 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (17 : BitVec 64) (18446744073709551613 : BitVec 64), 0) (fixture s 3 17 18446744073709551613) = _
 have numeric : (BitVec.umod (17 : BitVec 64) (18446744073709551613 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_5_1
example (s : riscv_state) : «dfn'REMU» (1,1,2) (fixture s 3 17 18446744073709551613) = (let t := fixture s 3 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 1 17 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 1) (fixture s 3 17 18446744073709551613) else «write'GPR» (BitVec.umod (17 : BitVec 64) (18446744073709551613 : BitVec 64), 1) (fixture s 3 17 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (17 : BitVec 64) (18446744073709551613 : BitVec 64), 1) (fixture s 3 17 18446744073709551613) = _
 have numeric : (BitVec.umod (17 : BitVec 64) (18446744073709551613 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_5_2
example (s : riscv_state) : «dfn'REMU» (2,1,2) (fixture s 3 17 18446744073709551613) = (let t := fixture s 3 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 2 17 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 2) (fixture s 3 17 18446744073709551613) else «write'GPR» (BitVec.umod (17 : BitVec 64) (18446744073709551613 : BitVec 64), 2) (fixture s 3 17 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (17 : BitVec 64) (18446744073709551613 : BitVec 64), 2) (fixture s 3 17 18446744073709551613) = _
 have numeric : (BitVec.umod (17 : BitVec 64) (18446744073709551613 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_5_7
example (s : riscv_state) : «dfn'REMU» (7,1,2) (fixture s 3 17 18446744073709551613) = (let t := fixture s 3 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 7 17 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((17 : BitVec 64), 7) (fixture s 3 17 18446744073709551613) else «write'GPR» (BitVec.umod (17 : BitVec 64) (18446744073709551613 : BitVec 64), 7) (fixture s 3 17 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (17 : BitVec 64) (18446744073709551613 : BitVec 64), 7) (fixture s 3 17 18446744073709551613) = _
 have numeric : (BitVec.umod (17 : BitVec 64) (18446744073709551613 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_6_0
example (s : riscv_state) : «dfn'REMU» (0,1,2) (fixture s 3 18446744073709551599 18446744073709551613) = (let t := fixture s 3 18446744073709551599 18446744073709551613; t) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551599 : BitVec 64), 0) (fixture s 3 18446744073709551599 18446744073709551613) else «write'GPR» (BitVec.umod (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 0) (fixture s 3 18446744073709551599 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 0) (fixture s 3 18446744073709551599 18446744073709551613) = _
 have numeric : (BitVec.umod (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64)) = (18446744073709551599 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_6_1
example (s : riscv_state) : «dfn'REMU» (1,1,2) (fixture s 3 18446744073709551599 18446744073709551613) = (let t := fixture s 3 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551599 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551599 : BitVec 64), 1) (fixture s 3 18446744073709551599 18446744073709551613) else «write'GPR» (BitVec.umod (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 1) (fixture s 3 18446744073709551599 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 1) (fixture s 3 18446744073709551599 18446744073709551613) = _
 have numeric : (BitVec.umod (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64)) = (18446744073709551599 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_6_2
example (s : riscv_state) : «dfn'REMU» (2,1,2) (fixture s 3 18446744073709551599 18446744073709551613) = (let t := fixture s 3 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551599 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551599 : BitVec 64), 2) (fixture s 3 18446744073709551599 18446744073709551613) else «write'GPR» (BitVec.umod (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 2) (fixture s 3 18446744073709551599 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 2) (fixture s 3 18446744073709551599 18446744073709551613) = _
 have numeric : (BitVec.umod (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64)) = (18446744073709551599 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_6_7
example (s : riscv_state) : «dfn'REMU» (7,1,2) (fixture s 3 18446744073709551599 18446744073709551613) = (let t := fixture s 3 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551599 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551599 : BitVec 64), 7) (fixture s 3 18446744073709551599 18446744073709551613) else «write'GPR» (BitVec.umod (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 7) (fixture s 3 18446744073709551599 18446744073709551613)) = _
 have divisorZero : ((18446744073709551613 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64), 7) (fixture s 3 18446744073709551599 18446744073709551613) = _
 have numeric : (BitVec.umod (18446744073709551599 : BitVec 64) (18446744073709551613 : BitVec 64)) = (18446744073709551599 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_7_0
example (s : riscv_state) : «dfn'REMU» (0,1,2) (fixture s 3 9223372036854775808 18446744073709551615) = (let t := fixture s 3 9223372036854775808 18446744073709551615; t) := by
 change (if ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((9223372036854775808 : BitVec 64), 0) (fixture s 3 9223372036854775808 18446744073709551615) else «write'GPR» (BitVec.umod (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 0) (fixture s 3 9223372036854775808 18446744073709551615)) = _
 have divisorZero : ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 0) (fixture s 3 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.umod (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64)) = (9223372036854775808 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_7_1
example (s : riscv_state) : «dfn'REMU» (1,1,2) (fixture s 3 9223372036854775808 18446744073709551615) = (let t := fixture s 3 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((9223372036854775808 : BitVec 64), 1) (fixture s 3 9223372036854775808 18446744073709551615) else «write'GPR» (BitVec.umod (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 1) (fixture s 3 9223372036854775808 18446744073709551615)) = _
 have divisorZero : ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 1) (fixture s 3 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.umod (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64)) = (9223372036854775808 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_7_2
example (s : riscv_state) : «dfn'REMU» (2,1,2) (fixture s 3 9223372036854775808 18446744073709551615) = (let t := fixture s 3 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((9223372036854775808 : BitVec 64), 2) (fixture s 3 9223372036854775808 18446744073709551615) else «write'GPR» (BitVec.umod (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 2) (fixture s 3 9223372036854775808 18446744073709551615)) = _
 have divisorZero : ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 2) (fixture s 3 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.umod (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64)) = (9223372036854775808 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_7_7
example (s : riscv_state) : «dfn'REMU» (7,1,2) (fixture s 3 9223372036854775808 18446744073709551615) = (let t := fixture s 3 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 9223372036854775808 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((9223372036854775808 : BitVec 64), 7) (fixture s 3 9223372036854775808 18446744073709551615) else «write'GPR» (BitVec.umod (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 7) (fixture s 3 9223372036854775808 18446744073709551615)) = _
 have divisorZero : ((18446744073709551615 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64), 7) (fixture s 3 9223372036854775808 18446744073709551615) = _
 have numeric : (BitVec.umod (9223372036854775808 : BitVec 64) (18446744073709551615 : BitVec 64)) = (9223372036854775808 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_8_0
example (s : riscv_state) : «dfn'REMU» (0,1,2) (fixture s 3 2147483648 4294967295) = (let t := fixture s 3 2147483648 4294967295; t) := by
 change (if ((4294967295 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((2147483648 : BitVec 64), 0) (fixture s 3 2147483648 4294967295) else «write'GPR» (BitVec.umod (2147483648 : BitVec 64) (4294967295 : BitVec 64), 0) (fixture s 3 2147483648 4294967295)) = _
 have divisorZero : ((4294967295 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (2147483648 : BitVec 64) (4294967295 : BitVec 64), 0) (fixture s 3 2147483648 4294967295) = _
 have numeric : (BitVec.umod (2147483648 : BitVec 64) (4294967295 : BitVec 64)) = (2147483648 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_8_1
example (s : riscv_state) : «dfn'REMU» (1,1,2) (fixture s 3 2147483648 4294967295) = (let t := fixture s 3 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 1 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967295 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((2147483648 : BitVec 64), 1) (fixture s 3 2147483648 4294967295) else «write'GPR» (BitVec.umod (2147483648 : BitVec 64) (4294967295 : BitVec 64), 1) (fixture s 3 2147483648 4294967295)) = _
 have divisorZero : ((4294967295 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (2147483648 : BitVec 64) (4294967295 : BitVec 64), 1) (fixture s 3 2147483648 4294967295) = _
 have numeric : (BitVec.umod (2147483648 : BitVec 64) (4294967295 : BitVec 64)) = (2147483648 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_8_2
example (s : riscv_state) : «dfn'REMU» (2,1,2) (fixture s 3 2147483648 4294967295) = (let t := fixture s 3 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 2 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967295 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((2147483648 : BitVec 64), 2) (fixture s 3 2147483648 4294967295) else «write'GPR» (BitVec.umod (2147483648 : BitVec 64) (4294967295 : BitVec 64), 2) (fixture s 3 2147483648 4294967295)) = _
 have divisorZero : ((4294967295 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (2147483648 : BitVec 64) (4294967295 : BitVec 64), 2) (fixture s 3 2147483648 4294967295) = _
 have numeric : (BitVec.umod (2147483648 : BitVec 64) (4294967295 : BitVec 64)) = (2147483648 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_8_7
example (s : riscv_state) : «dfn'REMU» (7,1,2) (fixture s 3 2147483648 4294967295) = (let t := fixture s 3 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 7 2147483648 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967295 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((2147483648 : BitVec 64), 7) (fixture s 3 2147483648 4294967295) else «write'GPR» (BitVec.umod (2147483648 : BitVec 64) (4294967295 : BitVec 64), 7) (fixture s 3 2147483648 4294967295)) = _
 have divisorZero : ((4294967295 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (2147483648 : BitVec 64) (4294967295 : BitVec 64), 7) (fixture s 3 2147483648 4294967295) = _
 have numeric : (BitVec.umod (2147483648 : BitVec 64) (4294967295 : BitVec 64)) = (2147483648 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_9_0
example (s : riscv_state) : «dfn'REMU» (0,1,2) (fixture s 3 4294967313 4294967296) = (let t := fixture s 3 4294967313 4294967296; t) := by
 change (if ((4294967296 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((4294967313 : BitVec 64), 0) (fixture s 3 4294967313 4294967296) else «write'GPR» (BitVec.umod (4294967313 : BitVec 64) (4294967296 : BitVec 64), 0) (fixture s 3 4294967313 4294967296)) = _
 have divisorZero : ((4294967296 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (4294967313 : BitVec 64) (4294967296 : BitVec 64), 0) (fixture s 3 4294967313 4294967296) = _
 have numeric : (BitVec.umod (4294967313 : BitVec 64) (4294967296 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_9_1
example (s : riscv_state) : «dfn'REMU» (1,1,2) (fixture s 3 4294967313 4294967296) = (let t := fixture s 3 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 1 17 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967296 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((4294967313 : BitVec 64), 1) (fixture s 3 4294967313 4294967296) else «write'GPR» (BitVec.umod (4294967313 : BitVec 64) (4294967296 : BitVec 64), 1) (fixture s 3 4294967313 4294967296)) = _
 have divisorZero : ((4294967296 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (4294967313 : BitVec 64) (4294967296 : BitVec 64), 1) (fixture s 3 4294967313 4294967296) = _
 have numeric : (BitVec.umod (4294967313 : BitVec 64) (4294967296 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_9_2
example (s : riscv_state) : «dfn'REMU» (2,1,2) (fixture s 3 4294967313 4294967296) = (let t := fixture s 3 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 2 17 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967296 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((4294967313 : BitVec 64), 2) (fixture s 3 4294967313 4294967296) else «write'GPR» (BitVec.umod (4294967313 : BitVec 64) (4294967296 : BitVec 64), 2) (fixture s 3 4294967313 4294967296)) = _
 have divisorZero : ((4294967296 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (4294967313 : BitVec 64) (4294967296 : BitVec 64), 2) (fixture s 3 4294967313 4294967296) = _
 have numeric : (BitVec.umod (4294967313 : BitVec 64) (4294967296 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_9_7
example (s : riscv_state) : «dfn'REMU» (7,1,2) (fixture s 3 4294967313 4294967296) = (let t := fixture s 3 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 7 17 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((4294967296 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((4294967313 : BitVec 64), 7) (fixture s 3 4294967313 4294967296) else «write'GPR» (BitVec.umod (4294967313 : BitVec 64) (4294967296 : BitVec 64), 7) (fixture s 3 4294967313 4294967296)) = _
 have divisorZero : ((4294967296 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (4294967313 : BitVec 64) (4294967296 : BitVec 64), 7) (fixture s 3 4294967313 4294967296) = _
 have numeric : (BitVec.umod (4294967313 : BitVec 64) (4294967296 : BitVec 64)) = (17 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_10_0
example (s : riscv_state) : «dfn'REMU» (0,1,2) (fixture s 3 18446744073709551615 2) = (let t := fixture s 3 18446744073709551615 2; t) := by
 change (if ((2 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 0) (fixture s 3 18446744073709551615 2) else «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (2 : BitVec 64), 0) (fixture s 3 18446744073709551615 2)) = _
 have divisorZero : ((2 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (2 : BitVec 64), 0) (fixture s 3 18446744073709551615 2) = _
 have numeric : (BitVec.umod (18446744073709551615 : BitVec 64) (2 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_10_1
example (s : riscv_state) : «dfn'REMU» (1,1,2) (fixture s 3 18446744073709551615 2) = (let t := fixture s 3 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((2 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 1) (fixture s 3 18446744073709551615 2) else «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (2 : BitVec 64), 1) (fixture s 3 18446744073709551615 2)) = _
 have divisorZero : ((2 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (2 : BitVec 64), 1) (fixture s 3 18446744073709551615 2) = _
 have numeric : (BitVec.umod (18446744073709551615 : BitVec 64) (2 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_10_2
example (s : riscv_state) : «dfn'REMU» (2,1,2) (fixture s 3 18446744073709551615 2) = (let t := fixture s 3 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((2 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 2) (fixture s 3 18446744073709551615 2) else «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (2 : BitVec 64), 2) (fixture s 3 18446744073709551615 2)) = _
 have divisorZero : ((2 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (2 : BitVec 64), 2) (fixture s 3 18446744073709551615 2) = _
 have numeric : (BitVec.umod (18446744073709551615 : BitVec 64) (2 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_10_7
example (s : riscv_state) : «dfn'REMU» (7,1,2) (fixture s 3 18446744073709551615 2) = (let t := fixture s 3 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((2 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 7) (fixture s 3 18446744073709551615 2) else «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (2 : BitVec 64), 7) (fixture s 3 18446744073709551615 2)) = _
 have divisorZero : ((2 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (2 : BitVec 64), 7) (fixture s 3 18446744073709551615 2) = _
 have numeric : (BitVec.umod (18446744073709551615 : BitVec 64) (2 : BitVec 64)) = (1 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_11_0
example (s : riscv_state) : «dfn'REMU» (0,1,2) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; t) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 0) (fixture s 3 18446744073709551615 3) else «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (3 : BitVec 64), 0) (fixture s 3 18446744073709551615 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (3 : BitVec 64), 0) (fixture s 3 18446744073709551615 3) = _
 have numeric : (BitVec.umod (18446744073709551615 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_11_1
example (s : riscv_state) : «dfn'REMU» (1,1,2) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 1) (fixture s 3 18446744073709551615 3) else «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (3 : BitVec 64), 1) (fixture s 3 18446744073709551615 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (3 : BitVec 64), 1) (fixture s 3 18446744073709551615 3) = _
 have numeric : (BitVec.umod (18446744073709551615 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_11_2
example (s : riscv_state) : «dfn'REMU» (2,1,2) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 2) (fixture s 3 18446744073709551615 3) else «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (3 : BitVec 64), 2) (fixture s 3 18446744073709551615 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (3 : BitVec 64), 2) (fixture s 3 18446744073709551615 3) = _
 have numeric : (BitVec.umod (18446744073709551615 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_11_7
example (s : riscv_state) : «dfn'REMU» (7,1,2) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 7) (fixture s 3 18446744073709551615 3) else «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (3 : BitVec 64), 7) (fixture s 3 18446744073709551615 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (3 : BitVec 64), 7) (fixture s 3 18446744073709551615 3) = _
 have numeric : (BitVec.umod (18446744073709551615 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_12_0
example (s : riscv_state) : «dfn'REMU» (0,0,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; t) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((0 : BitVec 64), 0) (fixture s 3 17 3) else «write'GPR» (BitVec.umod (0 : BitVec 64) (3 : BitVec 64), 0) (fixture s 3 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (0 : BitVec 64) (3 : BitVec 64), 0) (fixture s 3 17 3) = _
 have numeric : (BitVec.umod (0 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_12_1
example (s : riscv_state) : «dfn'REMU» (1,0,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((0 : BitVec 64), 1) (fixture s 3 17 3) else «write'GPR» (BitVec.umod (0 : BitVec 64) (3 : BitVec 64), 1) (fixture s 3 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (0 : BitVec 64) (3 : BitVec 64), 1) (fixture s 3 17 3) = _
 have numeric : (BitVec.umod (0 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_12_2
example (s : riscv_state) : «dfn'REMU» (2,0,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((0 : BitVec 64), 2) (fixture s 3 17 3) else «write'GPR» (BitVec.umod (0 : BitVec 64) (3 : BitVec 64), 2) (fixture s 3 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (0 : BitVec 64) (3 : BitVec 64), 2) (fixture s 3 17 3) = _
 have numeric : (BitVec.umod (0 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_12_7
example (s : riscv_state) : «dfn'REMU» (7,0,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((3 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((0 : BitVec 64), 7) (fixture s 3 17 3) else «write'GPR» (BitVec.umod (0 : BitVec 64) (3 : BitVec 64), 7) (fixture s 3 17 3)) = _
 have divisorZero : ((3 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (0 : BitVec 64) (3 : BitVec 64), 7) (fixture s 3 17 3) = _
 have numeric : (BitVec.umod (0 : BitVec 64) (3 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_13_0
example (s : riscv_state) : «dfn'REMU» (0,1,0) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; t) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 0) (fixture s 3 18446744073709551615 3) else «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (0 : BitVec 64), 0) (fixture s 3 18446744073709551615 3)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((18446744073709551615 : BitVec 64), 0) (fixture s 3 18446744073709551615 3) = _
 have numeric : ((18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_13_1
example (s : riscv_state) : «dfn'REMU» (1,1,0) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 1) (fixture s 3 18446744073709551615 3) else «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (0 : BitVec 64), 1) (fixture s 3 18446744073709551615 3)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((18446744073709551615 : BitVec 64), 1) (fixture s 3 18446744073709551615 3) = _
 have numeric : ((18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_13_2
example (s : riscv_state) : «dfn'REMU» (2,1,0) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 2) (fixture s 3 18446744073709551615 3) else «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (0 : BitVec 64), 2) (fixture s 3 18446744073709551615 3)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((18446744073709551615 : BitVec 64), 2) (fixture s 3 18446744073709551615 3) = _
 have numeric : ((18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_13_7
example (s : riscv_state) : «dfn'REMU» (7,1,0) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((0 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((18446744073709551615 : BitVec 64), 7) (fixture s 3 18446744073709551615 3) else «write'GPR» (BitVec.umod (18446744073709551615 : BitVec 64) (0 : BitVec 64), 7) (fixture s 3 18446744073709551615 3)) = _
 have divisorZero : ((0 : BitVec 64) == (0 : BitVec 64)) = true := by decide
 rw [divisorZero]
 change «write'GPR» ((18446744073709551615 : BitVec 64), 7) (fixture s 3 18446744073709551615 3) = _
 have numeric : ((18446744073709551615 : BitVec 64)) = (18446744073709551615 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_14_0
example (s : riscv_state) : «dfn'REMU» (0,1,1) (fixture s 3 9223372036854775808 2) = (let t := fixture s 3 9223372036854775808 2; t) := by
 change (if ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((9223372036854775808 : BitVec 64), 0) (fixture s 3 9223372036854775808 2) else «write'GPR» (BitVec.umod (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 0) (fixture s 3 9223372036854775808 2)) = _
 have divisorZero : ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 0) (fixture s 3 9223372036854775808 2) = _
 have numeric : (BitVec.umod (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_14_1
example (s : riscv_state) : «dfn'REMU» (1,1,1) (fixture s 3 9223372036854775808 2) = (let t := fixture s 3 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((9223372036854775808 : BitVec 64), 1) (fixture s 3 9223372036854775808 2) else «write'GPR» (BitVec.umod (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 1) (fixture s 3 9223372036854775808 2)) = _
 have divisorZero : ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 1) (fixture s 3 9223372036854775808 2) = _
 have numeric : (BitVec.umod (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_14_2
example (s : riscv_state) : «dfn'REMU» (2,1,1) (fixture s 3 9223372036854775808 2) = (let t := fixture s 3 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((9223372036854775808 : BitVec 64), 2) (fixture s 3 9223372036854775808 2) else «write'GPR» (BitVec.umod (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 2) (fixture s 3 9223372036854775808 2)) = _
 have divisorZero : ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 2) (fixture s 3 9223372036854775808 2) = _
 have numeric : (BitVec.umod (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_REMU_3_14_7
example (s : riscv_state) : «dfn'REMU» (7,1,1) (fixture s 3 9223372036854775808 2) = (let t := fixture s 3 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change (if ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) then «write'GPR» ((9223372036854775808 : BitVec 64), 7) (fixture s 3 9223372036854775808 2) else «write'GPR» (BitVec.umod (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 7) (fixture s 3 9223372036854775808 2)) = _
 have divisorZero : ((9223372036854775808 : BitVec 64) == (0 : BitVec 64)) = false := by decide
 rw [divisorZero]
 change «write'GPR» (BitVec.umod (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64), 7) (fixture s 3 9223372036854775808 2) = _
 have numeric : (BitVec.umod (9223372036854775808 : BitVec 64) (9223372036854775808 : BitVec 64)) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- divide_DIVW_0_0_0
example (s : riscv_state) : «dfn'DIVW» (0,1,2) (fixture s 0 0 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 0 0) := by rfl

-- divide_DIVW_0_0_1
example (s : riscv_state) : «dfn'DIVW» (1,1,2) (fixture s 0 0 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 0 0) := by rfl

-- divide_DIVW_0_0_2
example (s : riscv_state) : «dfn'DIVW» (2,1,2) (fixture s 0 0 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 0 0) := by rfl

-- divide_DIVW_0_0_7
example (s : riscv_state) : «dfn'DIVW» (7,1,2) (fixture s 0 0 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 0 0) := by rfl

-- divide_DIVW_0_1_0
example (s : riscv_state) : «dfn'DIVW» (0,1,2) (fixture s 0 17 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 0) := by rfl

-- divide_DIVW_0_1_1
example (s : riscv_state) : «dfn'DIVW» (1,1,2) (fixture s 0 17 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 0) := by rfl

-- divide_DIVW_0_1_2
example (s : riscv_state) : «dfn'DIVW» (2,1,2) (fixture s 0 17 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 0) := by rfl

-- divide_DIVW_0_1_7
example (s : riscv_state) : «dfn'DIVW» (7,1,2) (fixture s 0 17 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 0) := by rfl

-- divide_DIVW_0_2_0
example (s : riscv_state) : «dfn'DIVW» (0,1,2) (fixture s 0 18446744073709551615 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 0) := by rfl

-- divide_DIVW_0_2_1
example (s : riscv_state) : «dfn'DIVW» (1,1,2) (fixture s 0 18446744073709551615 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 0) := by rfl

-- divide_DIVW_0_2_2
example (s : riscv_state) : «dfn'DIVW» (2,1,2) (fixture s 0 18446744073709551615 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 0) := by rfl

-- divide_DIVW_0_2_7
example (s : riscv_state) : «dfn'DIVW» (7,1,2) (fixture s 0 18446744073709551615 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 0) := by rfl

-- divide_DIVW_0_3_0
example (s : riscv_state) : «dfn'DIVW» (0,1,2) (fixture s 0 17 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 3) := by rfl

-- divide_DIVW_0_3_1
example (s : riscv_state) : «dfn'DIVW» (1,1,2) (fixture s 0 17 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 3) := by rfl

-- divide_DIVW_0_3_2
example (s : riscv_state) : «dfn'DIVW» (2,1,2) (fixture s 0 17 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 3) := by rfl

-- divide_DIVW_0_3_7
example (s : riscv_state) : «dfn'DIVW» (7,1,2) (fixture s 0 17 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 3) := by rfl

-- divide_DIVW_0_4_0
example (s : riscv_state) : «dfn'DIVW» (0,1,2) (fixture s 0 18446744073709551599 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551599 3) := by rfl

-- divide_DIVW_0_4_1
example (s : riscv_state) : «dfn'DIVW» (1,1,2) (fixture s 0 18446744073709551599 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551599 3) := by rfl

-- divide_DIVW_0_4_2
example (s : riscv_state) : «dfn'DIVW» (2,1,2) (fixture s 0 18446744073709551599 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551599 3) := by rfl

-- divide_DIVW_0_4_7
example (s : riscv_state) : «dfn'DIVW» (7,1,2) (fixture s 0 18446744073709551599 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551599 3) := by rfl

-- divide_DIVW_0_5_0
example (s : riscv_state) : «dfn'DIVW» (0,1,2) (fixture s 0 17 18446744073709551613) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 18446744073709551613) := by rfl

-- divide_DIVW_0_5_1
example (s : riscv_state) : «dfn'DIVW» (1,1,2) (fixture s 0 17 18446744073709551613) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 18446744073709551613) := by rfl

-- divide_DIVW_0_5_2
example (s : riscv_state) : «dfn'DIVW» (2,1,2) (fixture s 0 17 18446744073709551613) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 18446744073709551613) := by rfl

-- divide_DIVW_0_5_7
example (s : riscv_state) : «dfn'DIVW» (7,1,2) (fixture s 0 17 18446744073709551613) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 18446744073709551613) := by rfl

-- divide_DIVW_0_6_0
example (s : riscv_state) : «dfn'DIVW» (0,1,2) (fixture s 0 18446744073709551599 18446744073709551613) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551599 18446744073709551613) := by rfl

-- divide_DIVW_0_6_1
example (s : riscv_state) : «dfn'DIVW» (1,1,2) (fixture s 0 18446744073709551599 18446744073709551613) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551599 18446744073709551613) := by rfl

-- divide_DIVW_0_6_2
example (s : riscv_state) : «dfn'DIVW» (2,1,2) (fixture s 0 18446744073709551599 18446744073709551613) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551599 18446744073709551613) := by rfl

-- divide_DIVW_0_6_7
example (s : riscv_state) : «dfn'DIVW» (7,1,2) (fixture s 0 18446744073709551599 18446744073709551613) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551599 18446744073709551613) := by rfl

-- divide_DIVW_0_7_0
example (s : riscv_state) : «dfn'DIVW» (0,1,2) (fixture s 0 9223372036854775808 18446744073709551615) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775808 18446744073709551615) := by rfl

-- divide_DIVW_0_7_1
example (s : riscv_state) : «dfn'DIVW» (1,1,2) (fixture s 0 9223372036854775808 18446744073709551615) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775808 18446744073709551615) := by rfl

-- divide_DIVW_0_7_2
example (s : riscv_state) : «dfn'DIVW» (2,1,2) (fixture s 0 9223372036854775808 18446744073709551615) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775808 18446744073709551615) := by rfl

-- divide_DIVW_0_7_7
example (s : riscv_state) : «dfn'DIVW» (7,1,2) (fixture s 0 9223372036854775808 18446744073709551615) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775808 18446744073709551615) := by rfl

-- divide_DIVW_0_8_0
example (s : riscv_state) : «dfn'DIVW» (0,1,2) (fixture s 0 2147483648 4294967295) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483648 4294967295) := by rfl

-- divide_DIVW_0_8_1
example (s : riscv_state) : «dfn'DIVW» (1,1,2) (fixture s 0 2147483648 4294967295) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483648 4294967295) := by rfl

-- divide_DIVW_0_8_2
example (s : riscv_state) : «dfn'DIVW» (2,1,2) (fixture s 0 2147483648 4294967295) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483648 4294967295) := by rfl

-- divide_DIVW_0_8_7
example (s : riscv_state) : «dfn'DIVW» (7,1,2) (fixture s 0 2147483648 4294967295) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483648 4294967295) := by rfl

-- divide_DIVW_0_9_0
example (s : riscv_state) : «dfn'DIVW» (0,1,2) (fixture s 0 4294967313 4294967296) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967313 4294967296) := by rfl

-- divide_DIVW_0_9_1
example (s : riscv_state) : «dfn'DIVW» (1,1,2) (fixture s 0 4294967313 4294967296) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967313 4294967296) := by rfl

-- divide_DIVW_0_9_2
example (s : riscv_state) : «dfn'DIVW» (2,1,2) (fixture s 0 4294967313 4294967296) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967313 4294967296) := by rfl

-- divide_DIVW_0_9_7
example (s : riscv_state) : «dfn'DIVW» (7,1,2) (fixture s 0 4294967313 4294967296) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967313 4294967296) := by rfl

-- divide_DIVW_0_10_0
example (s : riscv_state) : «dfn'DIVW» (0,1,2) (fixture s 0 18446744073709551615 2) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 2) := by rfl

-- divide_DIVW_0_10_1
example (s : riscv_state) : «dfn'DIVW» (1,1,2) (fixture s 0 18446744073709551615 2) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 2) := by rfl

-- divide_DIVW_0_10_2
example (s : riscv_state) : «dfn'DIVW» (2,1,2) (fixture s 0 18446744073709551615 2) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 2) := by rfl

-- divide_DIVW_0_10_7
example (s : riscv_state) : «dfn'DIVW» (7,1,2) (fixture s 0 18446744073709551615 2) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 2) := by rfl

-- divide_DIVW_0_11_0
example (s : riscv_state) : «dfn'DIVW» (0,1,2) (fixture s 0 18446744073709551615 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 3) := by rfl

-- divide_DIVW_0_11_1
example (s : riscv_state) : «dfn'DIVW» (1,1,2) (fixture s 0 18446744073709551615 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 3) := by rfl

-- divide_DIVW_0_11_2
example (s : riscv_state) : «dfn'DIVW» (2,1,2) (fixture s 0 18446744073709551615 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 3) := by rfl

-- divide_DIVW_0_11_7
example (s : riscv_state) : «dfn'DIVW» (7,1,2) (fixture s 0 18446744073709551615 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 3) := by rfl

-- divide_DIVW_0_12_0
example (s : riscv_state) : «dfn'DIVW» (0,0,2) (fixture s 0 17 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 3) := by rfl

-- divide_DIVW_0_12_1
example (s : riscv_state) : «dfn'DIVW» (1,0,2) (fixture s 0 17 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 3) := by rfl

-- divide_DIVW_0_12_2
example (s : riscv_state) : «dfn'DIVW» (2,0,2) (fixture s 0 17 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 3) := by rfl

-- divide_DIVW_0_12_7
example (s : riscv_state) : «dfn'DIVW» (7,0,2) (fixture s 0 17 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 3) := by rfl

-- divide_DIVW_0_13_0
example (s : riscv_state) : «dfn'DIVW» (0,1,0) (fixture s 0 18446744073709551615 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 3) := by rfl

-- divide_DIVW_0_13_1
example (s : riscv_state) : «dfn'DIVW» (1,1,0) (fixture s 0 18446744073709551615 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 3) := by rfl

-- divide_DIVW_0_13_2
example (s : riscv_state) : «dfn'DIVW» (2,1,0) (fixture s 0 18446744073709551615 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 3) := by rfl

-- divide_DIVW_0_13_7
example (s : riscv_state) : «dfn'DIVW» (7,1,0) (fixture s 0 18446744073709551615 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 3) := by rfl

-- divide_DIVW_0_14_0
example (s : riscv_state) : «dfn'DIVW» (0,1,1) (fixture s 0 9223372036854775808 2) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775808 2) := by rfl

-- divide_DIVW_0_14_1
example (s : riscv_state) : «dfn'DIVW» (1,1,1) (fixture s 0 9223372036854775808 2) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775808 2) := by rfl

-- divide_DIVW_0_14_2
example (s : riscv_state) : «dfn'DIVW» (2,1,1) (fixture s 0 9223372036854775808 2) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775808 2) := by rfl

-- divide_DIVW_0_14_7
example (s : riscv_state) : «dfn'DIVW» (7,1,1) (fixture s 0 9223372036854775808 2) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775808 2) := by rfl

-- divide_DIVW_2_0_0
example (s : riscv_state) : «dfn'DIVW» (0,1,2) (fixture s 2 0 0) = (let t := fixture s 2 0 0; t) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_0_1
example (s : riscv_state) : «dfn'DIVW» (1,1,2) (fixture s 2 0 0) = (let t := fixture s 2 0 0; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_0_2
example (s : riscv_state) : «dfn'DIVW» (2,1,2) (fixture s 2 0 0) = (let t := fixture s 2 0 0; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_0_7
example (s : riscv_state) : «dfn'DIVW» (7,1,2) (fixture s 2 0 0) = (let t := fixture s 2 0 0; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_1_0
example (s : riscv_state) : «dfn'DIVW» (0,1,2) (fixture s 2 17 0) = (let t := fixture s 2 17 0; t) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_1_1
example (s : riscv_state) : «dfn'DIVW» (1,1,2) (fixture s 2 17 0) = (let t := fixture s 2 17 0; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_1_2
example (s : riscv_state) : «dfn'DIVW» (2,1,2) (fixture s 2 17 0) = (let t := fixture s 2 17 0; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_1_7
example (s : riscv_state) : «dfn'DIVW» (7,1,2) (fixture s 2 17 0) = (let t := fixture s 2 17 0; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_2_0
example (s : riscv_state) : «dfn'DIVW» (0,1,2) (fixture s 2 18446744073709551615 0) = (let t := fixture s 2 18446744073709551615 0; t) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_2_1
example (s : riscv_state) : «dfn'DIVW» (1,1,2) (fixture s 2 18446744073709551615 0) = (let t := fixture s 2 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_2_2
example (s : riscv_state) : «dfn'DIVW» (2,1,2) (fixture s 2 18446744073709551615 0) = (let t := fixture s 2 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_2_7
example (s : riscv_state) : «dfn'DIVW» (7,1,2) (fixture s 2 18446744073709551615 0) = (let t := fixture s 2 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_3_0
example (s : riscv_state) : «dfn'DIVW» (0,1,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; t) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_3_1
example (s : riscv_state) : «dfn'DIVW» (1,1,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; {t with c_gpr := holUpdate 7 (holUpdate 1 5 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_3_2
example (s : riscv_state) : «dfn'DIVW» (2,1,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; {t with c_gpr := holUpdate 7 (holUpdate 2 5 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_3_7
example (s : riscv_state) : «dfn'DIVW» (7,1,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; {t with c_gpr := holUpdate 7 (holUpdate 7 5 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_4_0
example (s : riscv_state) : «dfn'DIVW» (0,1,2) (fixture s 2 18446744073709551599 3) = (let t := fixture s 2 18446744073709551599 3; t) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_4_1
example (s : riscv_state) : «dfn'DIVW» (1,1,2) (fixture s 2 18446744073709551599 3) = (let t := fixture s 2 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551611 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_4_2
example (s : riscv_state) : «dfn'DIVW» (2,1,2) (fixture s 2 18446744073709551599 3) = (let t := fixture s 2 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551611 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_4_7
example (s : riscv_state) : «dfn'DIVW» (7,1,2) (fixture s 2 18446744073709551599 3) = (let t := fixture s 2 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551611 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_5_0
example (s : riscv_state) : «dfn'DIVW» (0,1,2) (fixture s 2 17 18446744073709551613) = (let t := fixture s 2 17 18446744073709551613; t) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_5_1
example (s : riscv_state) : «dfn'DIVW» (1,1,2) (fixture s 2 17 18446744073709551613) = (let t := fixture s 2 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551611 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_5_2
example (s : riscv_state) : «dfn'DIVW» (2,1,2) (fixture s 2 17 18446744073709551613) = (let t := fixture s 2 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551611 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_5_7
example (s : riscv_state) : «dfn'DIVW» (7,1,2) (fixture s 2 17 18446744073709551613) = (let t := fixture s 2 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551611 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_6_0
example (s : riscv_state) : «dfn'DIVW» (0,1,2) (fixture s 2 18446744073709551599 18446744073709551613) = (let t := fixture s 2 18446744073709551599 18446744073709551613; t) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_6_1
example (s : riscv_state) : «dfn'DIVW» (1,1,2) (fixture s 2 18446744073709551599 18446744073709551613) = (let t := fixture s 2 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 1 5 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_6_2
example (s : riscv_state) : «dfn'DIVW» (2,1,2) (fixture s 2 18446744073709551599 18446744073709551613) = (let t := fixture s 2 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 2 5 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_6_7
example (s : riscv_state) : «dfn'DIVW» (7,1,2) (fixture s 2 18446744073709551599 18446744073709551613) = (let t := fixture s 2 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 7 5 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_7_0
example (s : riscv_state) : «dfn'DIVW» (0,1,2) (fixture s 2 9223372036854775808 18446744073709551615) = (let t := fixture s 2 9223372036854775808 18446744073709551615; t) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_7_1
example (s : riscv_state) : «dfn'DIVW» (1,1,2) (fixture s 2 9223372036854775808 18446744073709551615) = (let t := fixture s 2 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_7_2
example (s : riscv_state) : «dfn'DIVW» (2,1,2) (fixture s 2 9223372036854775808 18446744073709551615) = (let t := fixture s 2 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_7_7
example (s : riscv_state) : «dfn'DIVW» (7,1,2) (fixture s 2 9223372036854775808 18446744073709551615) = (let t := fixture s 2 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_8_0
example (s : riscv_state) : «dfn'DIVW» (0,1,2) (fixture s 2 2147483648 4294967295) = (let t := fixture s 2 2147483648 4294967295; t) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_8_1
example (s : riscv_state) : «dfn'DIVW» (1,1,2) (fixture s 2 2147483648 4294967295) = (let t := fixture s 2 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_8_2
example (s : riscv_state) : «dfn'DIVW» (2,1,2) (fixture s 2 2147483648 4294967295) = (let t := fixture s 2 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_8_7
example (s : riscv_state) : «dfn'DIVW» (7,1,2) (fixture s 2 2147483648 4294967295) = (let t := fixture s 2 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_9_0
example (s : riscv_state) : «dfn'DIVW» (0,1,2) (fixture s 2 4294967313 4294967296) = (let t := fixture s 2 4294967313 4294967296; t) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_9_1
example (s : riscv_state) : «dfn'DIVW» (1,1,2) (fixture s 2 4294967313 4294967296) = (let t := fixture s 2 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_9_2
example (s : riscv_state) : «dfn'DIVW» (2,1,2) (fixture s 2 4294967313 4294967296) = (let t := fixture s 2 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_9_7
example (s : riscv_state) : «dfn'DIVW» (7,1,2) (fixture s 2 4294967313 4294967296) = (let t := fixture s 2 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_10_0
example (s : riscv_state) : «dfn'DIVW» (0,1,2) (fixture s 2 18446744073709551615 2) = (let t := fixture s 2 18446744073709551615 2; t) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_10_1
example (s : riscv_state) : «dfn'DIVW» (1,1,2) (fixture s 2 18446744073709551615 2) = (let t := fixture s 2 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_10_2
example (s : riscv_state) : «dfn'DIVW» (2,1,2) (fixture s 2 18446744073709551615 2) = (let t := fixture s 2 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_10_7
example (s : riscv_state) : «dfn'DIVW» (7,1,2) (fixture s 2 18446744073709551615 2) = (let t := fixture s 2 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_11_0
example (s : riscv_state) : «dfn'DIVW» (0,1,2) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; t) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_11_1
example (s : riscv_state) : «dfn'DIVW» (1,1,2) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_11_2
example (s : riscv_state) : «dfn'DIVW» (2,1,2) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_11_7
example (s : riscv_state) : «dfn'DIVW» (7,1,2) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_12_0
example (s : riscv_state) : «dfn'DIVW» (0,0,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; t) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_12_1
example (s : riscv_state) : «dfn'DIVW» (1,0,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_12_2
example (s : riscv_state) : «dfn'DIVW» (2,0,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_12_7
example (s : riscv_state) : «dfn'DIVW» (7,0,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_13_0
example (s : riscv_state) : «dfn'DIVW» (0,1,0) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; t) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_13_1
example (s : riscv_state) : «dfn'DIVW» (1,1,0) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_13_2
example (s : riscv_state) : «dfn'DIVW» (2,1,0) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_13_7
example (s : riscv_state) : «dfn'DIVW» (7,1,0) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_14_0
example (s : riscv_state) : «dfn'DIVW» (0,1,1) (fixture s 2 9223372036854775808 2) = (let t := fixture s 2 9223372036854775808 2; t) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_14_1
example (s : riscv_state) : «dfn'DIVW» (1,1,1) (fixture s 2 9223372036854775808 2) = (let t := fixture s 2 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_14_2
example (s : riscv_state) : «dfn'DIVW» (2,1,1) (fixture s 2 9223372036854775808 2) = (let t := fixture s 2 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_2_14_7
example (s : riscv_state) : «dfn'DIVW» (7,1,1) (fixture s 2 9223372036854775808 2) = (let t := fixture s 2 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_0_0
example (s : riscv_state) : «dfn'DIVW» (0,1,2) (fixture s 3 0 0) = (let t := fixture s 3 0 0; t) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_0_1
example (s : riscv_state) : «dfn'DIVW» (1,1,2) (fixture s 3 0 0) = (let t := fixture s 3 0 0; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_0_2
example (s : riscv_state) : «dfn'DIVW» (2,1,2) (fixture s 3 0 0) = (let t := fixture s 3 0 0; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_0_7
example (s : riscv_state) : «dfn'DIVW» (7,1,2) (fixture s 3 0 0) = (let t := fixture s 3 0 0; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_1_0
example (s : riscv_state) : «dfn'DIVW» (0,1,2) (fixture s 3 17 0) = (let t := fixture s 3 17 0; t) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_1_1
example (s : riscv_state) : «dfn'DIVW» (1,1,2) (fixture s 3 17 0) = (let t := fixture s 3 17 0; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_1_2
example (s : riscv_state) : «dfn'DIVW» (2,1,2) (fixture s 3 17 0) = (let t := fixture s 3 17 0; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_1_7
example (s : riscv_state) : «dfn'DIVW» (7,1,2) (fixture s 3 17 0) = (let t := fixture s 3 17 0; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_2_0
example (s : riscv_state) : «dfn'DIVW» (0,1,2) (fixture s 3 18446744073709551615 0) = (let t := fixture s 3 18446744073709551615 0; t) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_2_1
example (s : riscv_state) : «dfn'DIVW» (1,1,2) (fixture s 3 18446744073709551615 0) = (let t := fixture s 3 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_2_2
example (s : riscv_state) : «dfn'DIVW» (2,1,2) (fixture s 3 18446744073709551615 0) = (let t := fixture s 3 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_2_7
example (s : riscv_state) : «dfn'DIVW» (7,1,2) (fixture s 3 18446744073709551615 0) = (let t := fixture s 3 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_3_0
example (s : riscv_state) : «dfn'DIVW» (0,1,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; t) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_3_1
example (s : riscv_state) : «dfn'DIVW» (1,1,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; {t with c_gpr := holUpdate 7 (holUpdate 1 5 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_3_2
example (s : riscv_state) : «dfn'DIVW» (2,1,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; {t with c_gpr := holUpdate 7 (holUpdate 2 5 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_3_7
example (s : riscv_state) : «dfn'DIVW» (7,1,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; {t with c_gpr := holUpdate 7 (holUpdate 7 5 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_4_0
example (s : riscv_state) : «dfn'DIVW» (0,1,2) (fixture s 3 18446744073709551599 3) = (let t := fixture s 3 18446744073709551599 3; t) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_4_1
example (s : riscv_state) : «dfn'DIVW» (1,1,2) (fixture s 3 18446744073709551599 3) = (let t := fixture s 3 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551611 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_4_2
example (s : riscv_state) : «dfn'DIVW» (2,1,2) (fixture s 3 18446744073709551599 3) = (let t := fixture s 3 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551611 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_4_7
example (s : riscv_state) : «dfn'DIVW» (7,1,2) (fixture s 3 18446744073709551599 3) = (let t := fixture s 3 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551611 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_5_0
example (s : riscv_state) : «dfn'DIVW» (0,1,2) (fixture s 3 17 18446744073709551613) = (let t := fixture s 3 17 18446744073709551613; t) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_5_1
example (s : riscv_state) : «dfn'DIVW» (1,1,2) (fixture s 3 17 18446744073709551613) = (let t := fixture s 3 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551611 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_5_2
example (s : riscv_state) : «dfn'DIVW» (2,1,2) (fixture s 3 17 18446744073709551613) = (let t := fixture s 3 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551611 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_5_7
example (s : riscv_state) : «dfn'DIVW» (7,1,2) (fixture s 3 17 18446744073709551613) = (let t := fixture s 3 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551611 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_6_0
example (s : riscv_state) : «dfn'DIVW» (0,1,2) (fixture s 3 18446744073709551599 18446744073709551613) = (let t := fixture s 3 18446744073709551599 18446744073709551613; t) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_6_1
example (s : riscv_state) : «dfn'DIVW» (1,1,2) (fixture s 3 18446744073709551599 18446744073709551613) = (let t := fixture s 3 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 1 5 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_6_2
example (s : riscv_state) : «dfn'DIVW» (2,1,2) (fixture s 3 18446744073709551599 18446744073709551613) = (let t := fixture s 3 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 2 5 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_6_7
example (s : riscv_state) : «dfn'DIVW» (7,1,2) (fixture s 3 18446744073709551599 18446744073709551613) = (let t := fixture s 3 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 7 5 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_7_0
example (s : riscv_state) : «dfn'DIVW» (0,1,2) (fixture s 3 9223372036854775808 18446744073709551615) = (let t := fixture s 3 9223372036854775808 18446744073709551615; t) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_7_1
example (s : riscv_state) : «dfn'DIVW» (1,1,2) (fixture s 3 9223372036854775808 18446744073709551615) = (let t := fixture s 3 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_7_2
example (s : riscv_state) : «dfn'DIVW» (2,1,2) (fixture s 3 9223372036854775808 18446744073709551615) = (let t := fixture s 3 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_7_7
example (s : riscv_state) : «dfn'DIVW» (7,1,2) (fixture s 3 9223372036854775808 18446744073709551615) = (let t := fixture s 3 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_8_0
example (s : riscv_state) : «dfn'DIVW» (0,1,2) (fixture s 3 2147483648 4294967295) = (let t := fixture s 3 2147483648 4294967295; t) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_8_1
example (s : riscv_state) : «dfn'DIVW» (1,1,2) (fixture s 3 2147483648 4294967295) = (let t := fixture s 3 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_8_2
example (s : riscv_state) : «dfn'DIVW» (2,1,2) (fixture s 3 2147483648 4294967295) = (let t := fixture s 3 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_8_7
example (s : riscv_state) : «dfn'DIVW» (7,1,2) (fixture s 3 2147483648 4294967295) = (let t := fixture s 3 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_9_0
example (s : riscv_state) : «dfn'DIVW» (0,1,2) (fixture s 3 4294967313 4294967296) = (let t := fixture s 3 4294967313 4294967296; t) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_9_1
example (s : riscv_state) : «dfn'DIVW» (1,1,2) (fixture s 3 4294967313 4294967296) = (let t := fixture s 3 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_9_2
example (s : riscv_state) : «dfn'DIVW» (2,1,2) (fixture s 3 4294967313 4294967296) = (let t := fixture s 3 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_9_7
example (s : riscv_state) : «dfn'DIVW» (7,1,2) (fixture s 3 4294967313 4294967296) = (let t := fixture s 3 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_10_0
example (s : riscv_state) : «dfn'DIVW» (0,1,2) (fixture s 3 18446744073709551615 2) = (let t := fixture s 3 18446744073709551615 2; t) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_10_1
example (s : riscv_state) : «dfn'DIVW» (1,1,2) (fixture s 3 18446744073709551615 2) = (let t := fixture s 3 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_10_2
example (s : riscv_state) : «dfn'DIVW» (2,1,2) (fixture s 3 18446744073709551615 2) = (let t := fixture s 3 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_10_7
example (s : riscv_state) : «dfn'DIVW» (7,1,2) (fixture s 3 18446744073709551615 2) = (let t := fixture s 3 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_11_0
example (s : riscv_state) : «dfn'DIVW» (0,1,2) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; t) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_11_1
example (s : riscv_state) : «dfn'DIVW» (1,1,2) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_11_2
example (s : riscv_state) : «dfn'DIVW» (2,1,2) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_11_7
example (s : riscv_state) : «dfn'DIVW» (7,1,2) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_12_0
example (s : riscv_state) : «dfn'DIVW» (0,0,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; t) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_12_1
example (s : riscv_state) : «dfn'DIVW» (1,0,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_12_2
example (s : riscv_state) : «dfn'DIVW» (2,0,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_12_7
example (s : riscv_state) : «dfn'DIVW» (7,0,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_13_0
example (s : riscv_state) : «dfn'DIVW» (0,1,0) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; t) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_13_1
example (s : riscv_state) : «dfn'DIVW» (1,1,0) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_13_2
example (s : riscv_state) : «dfn'DIVW» (2,1,0) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_13_7
example (s : riscv_state) : «dfn'DIVW» (7,1,0) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_14_0
example (s : riscv_state) : «dfn'DIVW» (0,1,1) (fixture s 3 9223372036854775808 2) = (let t := fixture s 3 9223372036854775808 2; t) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_14_1
example (s : riscv_state) : «dfn'DIVW» (1,1,1) (fixture s 3 9223372036854775808 2) = (let t := fixture s 3 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_14_2
example (s : riscv_state) : «dfn'DIVW» (2,1,1) (fixture s 3 9223372036854775808 2) = (let t := fixture s 3 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVW_3_14_7
example (s : riscv_state) : «dfn'DIVW» (7,1,1) (fixture s 3 9223372036854775808 2) = (let t := fixture s 3 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_0_0_0
example (s : riscv_state) : «dfn'REMW» (0,1,2) (fixture s 0 0 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 0 0) := by rfl

-- divide_REMW_0_0_1
example (s : riscv_state) : «dfn'REMW» (1,1,2) (fixture s 0 0 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 0 0) := by rfl

-- divide_REMW_0_0_2
example (s : riscv_state) : «dfn'REMW» (2,1,2) (fixture s 0 0 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 0 0) := by rfl

-- divide_REMW_0_0_7
example (s : riscv_state) : «dfn'REMW» (7,1,2) (fixture s 0 0 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 0 0) := by rfl

-- divide_REMW_0_1_0
example (s : riscv_state) : «dfn'REMW» (0,1,2) (fixture s 0 17 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 0) := by rfl

-- divide_REMW_0_1_1
example (s : riscv_state) : «dfn'REMW» (1,1,2) (fixture s 0 17 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 0) := by rfl

-- divide_REMW_0_1_2
example (s : riscv_state) : «dfn'REMW» (2,1,2) (fixture s 0 17 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 0) := by rfl

-- divide_REMW_0_1_7
example (s : riscv_state) : «dfn'REMW» (7,1,2) (fixture s 0 17 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 0) := by rfl

-- divide_REMW_0_2_0
example (s : riscv_state) : «dfn'REMW» (0,1,2) (fixture s 0 18446744073709551615 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 0) := by rfl

-- divide_REMW_0_2_1
example (s : riscv_state) : «dfn'REMW» (1,1,2) (fixture s 0 18446744073709551615 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 0) := by rfl

-- divide_REMW_0_2_2
example (s : riscv_state) : «dfn'REMW» (2,1,2) (fixture s 0 18446744073709551615 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 0) := by rfl

-- divide_REMW_0_2_7
example (s : riscv_state) : «dfn'REMW» (7,1,2) (fixture s 0 18446744073709551615 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 0) := by rfl

-- divide_REMW_0_3_0
example (s : riscv_state) : «dfn'REMW» (0,1,2) (fixture s 0 17 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 3) := by rfl

-- divide_REMW_0_3_1
example (s : riscv_state) : «dfn'REMW» (1,1,2) (fixture s 0 17 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 3) := by rfl

-- divide_REMW_0_3_2
example (s : riscv_state) : «dfn'REMW» (2,1,2) (fixture s 0 17 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 3) := by rfl

-- divide_REMW_0_3_7
example (s : riscv_state) : «dfn'REMW» (7,1,2) (fixture s 0 17 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 3) := by rfl

-- divide_REMW_0_4_0
example (s : riscv_state) : «dfn'REMW» (0,1,2) (fixture s 0 18446744073709551599 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551599 3) := by rfl

-- divide_REMW_0_4_1
example (s : riscv_state) : «dfn'REMW» (1,1,2) (fixture s 0 18446744073709551599 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551599 3) := by rfl

-- divide_REMW_0_4_2
example (s : riscv_state) : «dfn'REMW» (2,1,2) (fixture s 0 18446744073709551599 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551599 3) := by rfl

-- divide_REMW_0_4_7
example (s : riscv_state) : «dfn'REMW» (7,1,2) (fixture s 0 18446744073709551599 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551599 3) := by rfl

-- divide_REMW_0_5_0
example (s : riscv_state) : «dfn'REMW» (0,1,2) (fixture s 0 17 18446744073709551613) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 18446744073709551613) := by rfl

-- divide_REMW_0_5_1
example (s : riscv_state) : «dfn'REMW» (1,1,2) (fixture s 0 17 18446744073709551613) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 18446744073709551613) := by rfl

-- divide_REMW_0_5_2
example (s : riscv_state) : «dfn'REMW» (2,1,2) (fixture s 0 17 18446744073709551613) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 18446744073709551613) := by rfl

-- divide_REMW_0_5_7
example (s : riscv_state) : «dfn'REMW» (7,1,2) (fixture s 0 17 18446744073709551613) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 18446744073709551613) := by rfl

-- divide_REMW_0_6_0
example (s : riscv_state) : «dfn'REMW» (0,1,2) (fixture s 0 18446744073709551599 18446744073709551613) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551599 18446744073709551613) := by rfl

-- divide_REMW_0_6_1
example (s : riscv_state) : «dfn'REMW» (1,1,2) (fixture s 0 18446744073709551599 18446744073709551613) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551599 18446744073709551613) := by rfl

-- divide_REMW_0_6_2
example (s : riscv_state) : «dfn'REMW» (2,1,2) (fixture s 0 18446744073709551599 18446744073709551613) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551599 18446744073709551613) := by rfl

-- divide_REMW_0_6_7
example (s : riscv_state) : «dfn'REMW» (7,1,2) (fixture s 0 18446744073709551599 18446744073709551613) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551599 18446744073709551613) := by rfl

-- divide_REMW_0_7_0
example (s : riscv_state) : «dfn'REMW» (0,1,2) (fixture s 0 9223372036854775808 18446744073709551615) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775808 18446744073709551615) := by rfl

-- divide_REMW_0_7_1
example (s : riscv_state) : «dfn'REMW» (1,1,2) (fixture s 0 9223372036854775808 18446744073709551615) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775808 18446744073709551615) := by rfl

-- divide_REMW_0_7_2
example (s : riscv_state) : «dfn'REMW» (2,1,2) (fixture s 0 9223372036854775808 18446744073709551615) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775808 18446744073709551615) := by rfl

-- divide_REMW_0_7_7
example (s : riscv_state) : «dfn'REMW» (7,1,2) (fixture s 0 9223372036854775808 18446744073709551615) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775808 18446744073709551615) := by rfl

-- divide_REMW_0_8_0
example (s : riscv_state) : «dfn'REMW» (0,1,2) (fixture s 0 2147483648 4294967295) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483648 4294967295) := by rfl

-- divide_REMW_0_8_1
example (s : riscv_state) : «dfn'REMW» (1,1,2) (fixture s 0 2147483648 4294967295) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483648 4294967295) := by rfl

-- divide_REMW_0_8_2
example (s : riscv_state) : «dfn'REMW» (2,1,2) (fixture s 0 2147483648 4294967295) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483648 4294967295) := by rfl

-- divide_REMW_0_8_7
example (s : riscv_state) : «dfn'REMW» (7,1,2) (fixture s 0 2147483648 4294967295) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483648 4294967295) := by rfl

-- divide_REMW_0_9_0
example (s : riscv_state) : «dfn'REMW» (0,1,2) (fixture s 0 4294967313 4294967296) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967313 4294967296) := by rfl

-- divide_REMW_0_9_1
example (s : riscv_state) : «dfn'REMW» (1,1,2) (fixture s 0 4294967313 4294967296) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967313 4294967296) := by rfl

-- divide_REMW_0_9_2
example (s : riscv_state) : «dfn'REMW» (2,1,2) (fixture s 0 4294967313 4294967296) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967313 4294967296) := by rfl

-- divide_REMW_0_9_7
example (s : riscv_state) : «dfn'REMW» (7,1,2) (fixture s 0 4294967313 4294967296) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967313 4294967296) := by rfl

-- divide_REMW_0_10_0
example (s : riscv_state) : «dfn'REMW» (0,1,2) (fixture s 0 18446744073709551615 2) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 2) := by rfl

-- divide_REMW_0_10_1
example (s : riscv_state) : «dfn'REMW» (1,1,2) (fixture s 0 18446744073709551615 2) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 2) := by rfl

-- divide_REMW_0_10_2
example (s : riscv_state) : «dfn'REMW» (2,1,2) (fixture s 0 18446744073709551615 2) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 2) := by rfl

-- divide_REMW_0_10_7
example (s : riscv_state) : «dfn'REMW» (7,1,2) (fixture s 0 18446744073709551615 2) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 2) := by rfl

-- divide_REMW_0_11_0
example (s : riscv_state) : «dfn'REMW» (0,1,2) (fixture s 0 18446744073709551615 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 3) := by rfl

-- divide_REMW_0_11_1
example (s : riscv_state) : «dfn'REMW» (1,1,2) (fixture s 0 18446744073709551615 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 3) := by rfl

-- divide_REMW_0_11_2
example (s : riscv_state) : «dfn'REMW» (2,1,2) (fixture s 0 18446744073709551615 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 3) := by rfl

-- divide_REMW_0_11_7
example (s : riscv_state) : «dfn'REMW» (7,1,2) (fixture s 0 18446744073709551615 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 3) := by rfl

-- divide_REMW_0_12_0
example (s : riscv_state) : «dfn'REMW» (0,0,2) (fixture s 0 17 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 3) := by rfl

-- divide_REMW_0_12_1
example (s : riscv_state) : «dfn'REMW» (1,0,2) (fixture s 0 17 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 3) := by rfl

-- divide_REMW_0_12_2
example (s : riscv_state) : «dfn'REMW» (2,0,2) (fixture s 0 17 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 3) := by rfl

-- divide_REMW_0_12_7
example (s : riscv_state) : «dfn'REMW» (7,0,2) (fixture s 0 17 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 3) := by rfl

-- divide_REMW_0_13_0
example (s : riscv_state) : «dfn'REMW» (0,1,0) (fixture s 0 18446744073709551615 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 3) := by rfl

-- divide_REMW_0_13_1
example (s : riscv_state) : «dfn'REMW» (1,1,0) (fixture s 0 18446744073709551615 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 3) := by rfl

-- divide_REMW_0_13_2
example (s : riscv_state) : «dfn'REMW» (2,1,0) (fixture s 0 18446744073709551615 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 3) := by rfl

-- divide_REMW_0_13_7
example (s : riscv_state) : «dfn'REMW» (7,1,0) (fixture s 0 18446744073709551615 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 3) := by rfl

-- divide_REMW_0_14_0
example (s : riscv_state) : «dfn'REMW» (0,1,1) (fixture s 0 9223372036854775808 2) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775808 2) := by rfl

-- divide_REMW_0_14_1
example (s : riscv_state) : «dfn'REMW» (1,1,1) (fixture s 0 9223372036854775808 2) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775808 2) := by rfl

-- divide_REMW_0_14_2
example (s : riscv_state) : «dfn'REMW» (2,1,1) (fixture s 0 9223372036854775808 2) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775808 2) := by rfl

-- divide_REMW_0_14_7
example (s : riscv_state) : «dfn'REMW» (7,1,1) (fixture s 0 9223372036854775808 2) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775808 2) := by rfl

-- divide_REMW_2_0_0
example (s : riscv_state) : «dfn'REMW» (0,1,2) (fixture s 2 0 0) = (let t := fixture s 2 0 0; t) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_0_1
example (s : riscv_state) : «dfn'REMW» (1,1,2) (fixture s 2 0 0) = (let t := fixture s 2 0 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_0_2
example (s : riscv_state) : «dfn'REMW» (2,1,2) (fixture s 2 0 0) = (let t := fixture s 2 0 0; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_0_7
example (s : riscv_state) : «dfn'REMW» (7,1,2) (fixture s 2 0 0) = (let t := fixture s 2 0 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_1_0
example (s : riscv_state) : «dfn'REMW» (0,1,2) (fixture s 2 17 0) = (let t := fixture s 2 17 0; t) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_1_1
example (s : riscv_state) : «dfn'REMW» (1,1,2) (fixture s 2 17 0) = (let t := fixture s 2 17 0; {t with c_gpr := holUpdate 7 (holUpdate 1 17 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_1_2
example (s : riscv_state) : «dfn'REMW» (2,1,2) (fixture s 2 17 0) = (let t := fixture s 2 17 0; {t with c_gpr := holUpdate 7 (holUpdate 2 17 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_1_7
example (s : riscv_state) : «dfn'REMW» (7,1,2) (fixture s 2 17 0) = (let t := fixture s 2 17 0; {t with c_gpr := holUpdate 7 (holUpdate 7 17 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_2_0
example (s : riscv_state) : «dfn'REMW» (0,1,2) (fixture s 2 18446744073709551615 0) = (let t := fixture s 2 18446744073709551615 0; t) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_2_1
example (s : riscv_state) : «dfn'REMW» (1,1,2) (fixture s 2 18446744073709551615 0) = (let t := fixture s 2 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_2_2
example (s : riscv_state) : «dfn'REMW» (2,1,2) (fixture s 2 18446744073709551615 0) = (let t := fixture s 2 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_2_7
example (s : riscv_state) : «dfn'REMW» (7,1,2) (fixture s 2 18446744073709551615 0) = (let t := fixture s 2 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_3_0
example (s : riscv_state) : «dfn'REMW» (0,1,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; t) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_3_1
example (s : riscv_state) : «dfn'REMW» (1,1,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; {t with c_gpr := holUpdate 7 (holUpdate 1 2 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_3_2
example (s : riscv_state) : «dfn'REMW» (2,1,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; {t with c_gpr := holUpdate 7 (holUpdate 2 2 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_3_7
example (s : riscv_state) : «dfn'REMW» (7,1,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; {t with c_gpr := holUpdate 7 (holUpdate 7 2 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_4_0
example (s : riscv_state) : «dfn'REMW» (0,1,2) (fixture s 2 18446744073709551599 3) = (let t := fixture s 2 18446744073709551599 3; t) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_4_1
example (s : riscv_state) : «dfn'REMW» (1,1,2) (fixture s 2 18446744073709551599 3) = (let t := fixture s 2 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_4_2
example (s : riscv_state) : «dfn'REMW» (2,1,2) (fixture s 2 18446744073709551599 3) = (let t := fixture s 2 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_4_7
example (s : riscv_state) : «dfn'REMW» (7,1,2) (fixture s 2 18446744073709551599 3) = (let t := fixture s 2 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_5_0
example (s : riscv_state) : «dfn'REMW» (0,1,2) (fixture s 2 17 18446744073709551613) = (let t := fixture s 2 17 18446744073709551613; t) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_5_1
example (s : riscv_state) : «dfn'REMW» (1,1,2) (fixture s 2 17 18446744073709551613) = (let t := fixture s 2 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 1 2 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_5_2
example (s : riscv_state) : «dfn'REMW» (2,1,2) (fixture s 2 17 18446744073709551613) = (let t := fixture s 2 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 2 2 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_5_7
example (s : riscv_state) : «dfn'REMW» (7,1,2) (fixture s 2 17 18446744073709551613) = (let t := fixture s 2 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 7 2 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_6_0
example (s : riscv_state) : «dfn'REMW» (0,1,2) (fixture s 2 18446744073709551599 18446744073709551613) = (let t := fixture s 2 18446744073709551599 18446744073709551613; t) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_6_1
example (s : riscv_state) : «dfn'REMW» (1,1,2) (fixture s 2 18446744073709551599 18446744073709551613) = (let t := fixture s 2 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_6_2
example (s : riscv_state) : «dfn'REMW» (2,1,2) (fixture s 2 18446744073709551599 18446744073709551613) = (let t := fixture s 2 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_6_7
example (s : riscv_state) : «dfn'REMW» (7,1,2) (fixture s 2 18446744073709551599 18446744073709551613) = (let t := fixture s 2 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_7_0
example (s : riscv_state) : «dfn'REMW» (0,1,2) (fixture s 2 9223372036854775808 18446744073709551615) = (let t := fixture s 2 9223372036854775808 18446744073709551615; t) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_7_1
example (s : riscv_state) : «dfn'REMW» (1,1,2) (fixture s 2 9223372036854775808 18446744073709551615) = (let t := fixture s 2 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_7_2
example (s : riscv_state) : «dfn'REMW» (2,1,2) (fixture s 2 9223372036854775808 18446744073709551615) = (let t := fixture s 2 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_7_7
example (s : riscv_state) : «dfn'REMW» (7,1,2) (fixture s 2 9223372036854775808 18446744073709551615) = (let t := fixture s 2 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_8_0
example (s : riscv_state) : «dfn'REMW» (0,1,2) (fixture s 2 2147483648 4294967295) = (let t := fixture s 2 2147483648 4294967295; t) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_8_1
example (s : riscv_state) : «dfn'REMW» (1,1,2) (fixture s 2 2147483648 4294967295) = (let t := fixture s 2 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_8_2
example (s : riscv_state) : «dfn'REMW» (2,1,2) (fixture s 2 2147483648 4294967295) = (let t := fixture s 2 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_8_7
example (s : riscv_state) : «dfn'REMW» (7,1,2) (fixture s 2 2147483648 4294967295) = (let t := fixture s 2 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_9_0
example (s : riscv_state) : «dfn'REMW» (0,1,2) (fixture s 2 4294967313 4294967296) = (let t := fixture s 2 4294967313 4294967296; t) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_9_1
example (s : riscv_state) : «dfn'REMW» (1,1,2) (fixture s 2 4294967313 4294967296) = (let t := fixture s 2 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 1 17 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_9_2
example (s : riscv_state) : «dfn'REMW» (2,1,2) (fixture s 2 4294967313 4294967296) = (let t := fixture s 2 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 2 17 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_9_7
example (s : riscv_state) : «dfn'REMW» (7,1,2) (fixture s 2 4294967313 4294967296) = (let t := fixture s 2 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 7 17 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_10_0
example (s : riscv_state) : «dfn'REMW» (0,1,2) (fixture s 2 18446744073709551615 2) = (let t := fixture s 2 18446744073709551615 2; t) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_10_1
example (s : riscv_state) : «dfn'REMW» (1,1,2) (fixture s 2 18446744073709551615 2) = (let t := fixture s 2 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_10_2
example (s : riscv_state) : «dfn'REMW» (2,1,2) (fixture s 2 18446744073709551615 2) = (let t := fixture s 2 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_10_7
example (s : riscv_state) : «dfn'REMW» (7,1,2) (fixture s 2 18446744073709551615 2) = (let t := fixture s 2 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_11_0
example (s : riscv_state) : «dfn'REMW» (0,1,2) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; t) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_11_1
example (s : riscv_state) : «dfn'REMW» (1,1,2) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_11_2
example (s : riscv_state) : «dfn'REMW» (2,1,2) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_11_7
example (s : riscv_state) : «dfn'REMW» (7,1,2) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_12_0
example (s : riscv_state) : «dfn'REMW» (0,0,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; t) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_12_1
example (s : riscv_state) : «dfn'REMW» (1,0,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_12_2
example (s : riscv_state) : «dfn'REMW» (2,0,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_12_7
example (s : riscv_state) : «dfn'REMW» (7,0,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_13_0
example (s : riscv_state) : «dfn'REMW» (0,1,0) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; t) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_13_1
example (s : riscv_state) : «dfn'REMW» (1,1,0) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_13_2
example (s : riscv_state) : «dfn'REMW» (2,1,0) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_13_7
example (s : riscv_state) : «dfn'REMW» (7,1,0) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_14_0
example (s : riscv_state) : «dfn'REMW» (0,1,1) (fixture s 2 9223372036854775808 2) = (let t := fixture s 2 9223372036854775808 2; t) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_14_1
example (s : riscv_state) : «dfn'REMW» (1,1,1) (fixture s 2 9223372036854775808 2) = (let t := fixture s 2 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_14_2
example (s : riscv_state) : «dfn'REMW» (2,1,1) (fixture s 2 9223372036854775808 2) = (let t := fixture s 2 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_2_14_7
example (s : riscv_state) : «dfn'REMW» (7,1,1) (fixture s 2 9223372036854775808 2) = (let t := fixture s 2 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_0_0
example (s : riscv_state) : «dfn'REMW» (0,1,2) (fixture s 3 0 0) = (let t := fixture s 3 0 0; t) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_0_1
example (s : riscv_state) : «dfn'REMW» (1,1,2) (fixture s 3 0 0) = (let t := fixture s 3 0 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_0_2
example (s : riscv_state) : «dfn'REMW» (2,1,2) (fixture s 3 0 0) = (let t := fixture s 3 0 0; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_0_7
example (s : riscv_state) : «dfn'REMW» (7,1,2) (fixture s 3 0 0) = (let t := fixture s 3 0 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_1_0
example (s : riscv_state) : «dfn'REMW» (0,1,2) (fixture s 3 17 0) = (let t := fixture s 3 17 0; t) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_1_1
example (s : riscv_state) : «dfn'REMW» (1,1,2) (fixture s 3 17 0) = (let t := fixture s 3 17 0; {t with c_gpr := holUpdate 7 (holUpdate 1 17 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_1_2
example (s : riscv_state) : «dfn'REMW» (2,1,2) (fixture s 3 17 0) = (let t := fixture s 3 17 0; {t with c_gpr := holUpdate 7 (holUpdate 2 17 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_1_7
example (s : riscv_state) : «dfn'REMW» (7,1,2) (fixture s 3 17 0) = (let t := fixture s 3 17 0; {t with c_gpr := holUpdate 7 (holUpdate 7 17 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_2_0
example (s : riscv_state) : «dfn'REMW» (0,1,2) (fixture s 3 18446744073709551615 0) = (let t := fixture s 3 18446744073709551615 0; t) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_2_1
example (s : riscv_state) : «dfn'REMW» (1,1,2) (fixture s 3 18446744073709551615 0) = (let t := fixture s 3 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_2_2
example (s : riscv_state) : «dfn'REMW» (2,1,2) (fixture s 3 18446744073709551615 0) = (let t := fixture s 3 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_2_7
example (s : riscv_state) : «dfn'REMW» (7,1,2) (fixture s 3 18446744073709551615 0) = (let t := fixture s 3 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_3_0
example (s : riscv_state) : «dfn'REMW» (0,1,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; t) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_3_1
example (s : riscv_state) : «dfn'REMW» (1,1,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; {t with c_gpr := holUpdate 7 (holUpdate 1 2 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_3_2
example (s : riscv_state) : «dfn'REMW» (2,1,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; {t with c_gpr := holUpdate 7 (holUpdate 2 2 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_3_7
example (s : riscv_state) : «dfn'REMW» (7,1,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; {t with c_gpr := holUpdate 7 (holUpdate 7 2 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_4_0
example (s : riscv_state) : «dfn'REMW» (0,1,2) (fixture s 3 18446744073709551599 3) = (let t := fixture s 3 18446744073709551599 3; t) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_4_1
example (s : riscv_state) : «dfn'REMW» (1,1,2) (fixture s 3 18446744073709551599 3) = (let t := fixture s 3 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_4_2
example (s : riscv_state) : «dfn'REMW» (2,1,2) (fixture s 3 18446744073709551599 3) = (let t := fixture s 3 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_4_7
example (s : riscv_state) : «dfn'REMW» (7,1,2) (fixture s 3 18446744073709551599 3) = (let t := fixture s 3 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_5_0
example (s : riscv_state) : «dfn'REMW» (0,1,2) (fixture s 3 17 18446744073709551613) = (let t := fixture s 3 17 18446744073709551613; t) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_5_1
example (s : riscv_state) : «dfn'REMW» (1,1,2) (fixture s 3 17 18446744073709551613) = (let t := fixture s 3 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 1 2 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_5_2
example (s : riscv_state) : «dfn'REMW» (2,1,2) (fixture s 3 17 18446744073709551613) = (let t := fixture s 3 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 2 2 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_5_7
example (s : riscv_state) : «dfn'REMW» (7,1,2) (fixture s 3 17 18446744073709551613) = (let t := fixture s 3 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 7 2 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_6_0
example (s : riscv_state) : «dfn'REMW» (0,1,2) (fixture s 3 18446744073709551599 18446744073709551613) = (let t := fixture s 3 18446744073709551599 18446744073709551613; t) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_6_1
example (s : riscv_state) : «dfn'REMW» (1,1,2) (fixture s 3 18446744073709551599 18446744073709551613) = (let t := fixture s 3 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_6_2
example (s : riscv_state) : «dfn'REMW» (2,1,2) (fixture s 3 18446744073709551599 18446744073709551613) = (let t := fixture s 3 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_6_7
example (s : riscv_state) : «dfn'REMW» (7,1,2) (fixture s 3 18446744073709551599 18446744073709551613) = (let t := fixture s 3 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551614 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_7_0
example (s : riscv_state) : «dfn'REMW» (0,1,2) (fixture s 3 9223372036854775808 18446744073709551615) = (let t := fixture s 3 9223372036854775808 18446744073709551615; t) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_7_1
example (s : riscv_state) : «dfn'REMW» (1,1,2) (fixture s 3 9223372036854775808 18446744073709551615) = (let t := fixture s 3 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_7_2
example (s : riscv_state) : «dfn'REMW» (2,1,2) (fixture s 3 9223372036854775808 18446744073709551615) = (let t := fixture s 3 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_7_7
example (s : riscv_state) : «dfn'REMW» (7,1,2) (fixture s 3 9223372036854775808 18446744073709551615) = (let t := fixture s 3 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_8_0
example (s : riscv_state) : «dfn'REMW» (0,1,2) (fixture s 3 2147483648 4294967295) = (let t := fixture s 3 2147483648 4294967295; t) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_8_1
example (s : riscv_state) : «dfn'REMW» (1,1,2) (fixture s 3 2147483648 4294967295) = (let t := fixture s 3 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_8_2
example (s : riscv_state) : «dfn'REMW» (2,1,2) (fixture s 3 2147483648 4294967295) = (let t := fixture s 3 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_8_7
example (s : riscv_state) : «dfn'REMW» (7,1,2) (fixture s 3 2147483648 4294967295) = (let t := fixture s 3 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_9_0
example (s : riscv_state) : «dfn'REMW» (0,1,2) (fixture s 3 4294967313 4294967296) = (let t := fixture s 3 4294967313 4294967296; t) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_9_1
example (s : riscv_state) : «dfn'REMW» (1,1,2) (fixture s 3 4294967313 4294967296) = (let t := fixture s 3 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 1 17 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_9_2
example (s : riscv_state) : «dfn'REMW» (2,1,2) (fixture s 3 4294967313 4294967296) = (let t := fixture s 3 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 2 17 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_9_7
example (s : riscv_state) : «dfn'REMW» (7,1,2) (fixture s 3 4294967313 4294967296) = (let t := fixture s 3 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 7 17 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_10_0
example (s : riscv_state) : «dfn'REMW» (0,1,2) (fixture s 3 18446744073709551615 2) = (let t := fixture s 3 18446744073709551615 2; t) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_10_1
example (s : riscv_state) : «dfn'REMW» (1,1,2) (fixture s 3 18446744073709551615 2) = (let t := fixture s 3 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_10_2
example (s : riscv_state) : «dfn'REMW» (2,1,2) (fixture s 3 18446744073709551615 2) = (let t := fixture s 3 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_10_7
example (s : riscv_state) : «dfn'REMW» (7,1,2) (fixture s 3 18446744073709551615 2) = (let t := fixture s 3 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_11_0
example (s : riscv_state) : «dfn'REMW» (0,1,2) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; t) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_11_1
example (s : riscv_state) : «dfn'REMW» (1,1,2) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_11_2
example (s : riscv_state) : «dfn'REMW» (2,1,2) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_11_7
example (s : riscv_state) : «dfn'REMW» (7,1,2) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_12_0
example (s : riscv_state) : «dfn'REMW» (0,0,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; t) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_12_1
example (s : riscv_state) : «dfn'REMW» (1,0,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_12_2
example (s : riscv_state) : «dfn'REMW» (2,0,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_12_7
example (s : riscv_state) : «dfn'REMW» (7,0,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_13_0
example (s : riscv_state) : «dfn'REMW» (0,1,0) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; t) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_13_1
example (s : riscv_state) : «dfn'REMW» (1,1,0) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_13_2
example (s : riscv_state) : «dfn'REMW» (2,1,0) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_13_7
example (s : riscv_state) : «dfn'REMW» (7,1,0) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_14_0
example (s : riscv_state) : «dfn'REMW» (0,1,1) (fixture s 3 9223372036854775808 2) = (let t := fixture s 3 9223372036854775808 2; t) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_14_1
example (s : riscv_state) : «dfn'REMW» (1,1,1) (fixture s 3 9223372036854775808 2) = (let t := fixture s 3 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_14_2
example (s : riscv_state) : «dfn'REMW» (2,1,1) (fixture s 3 9223372036854775808 2) = (let t := fixture s 3 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMW_3_14_7
example (s : riscv_state) : «dfn'REMW» (7,1,1) (fixture s 3 9223372036854775808 2) = (let t := fixture s 3 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_0_0_0
example (s : riscv_state) : «dfn'DIVUW» (0,1,2) (fixture s 0 0 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 0 0) := by rfl

-- divide_DIVUW_0_0_1
example (s : riscv_state) : «dfn'DIVUW» (1,1,2) (fixture s 0 0 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 0 0) := by rfl

-- divide_DIVUW_0_0_2
example (s : riscv_state) : «dfn'DIVUW» (2,1,2) (fixture s 0 0 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 0 0) := by rfl

-- divide_DIVUW_0_0_7
example (s : riscv_state) : «dfn'DIVUW» (7,1,2) (fixture s 0 0 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 0 0) := by rfl

-- divide_DIVUW_0_1_0
example (s : riscv_state) : «dfn'DIVUW» (0,1,2) (fixture s 0 17 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 0) := by rfl

-- divide_DIVUW_0_1_1
example (s : riscv_state) : «dfn'DIVUW» (1,1,2) (fixture s 0 17 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 0) := by rfl

-- divide_DIVUW_0_1_2
example (s : riscv_state) : «dfn'DIVUW» (2,1,2) (fixture s 0 17 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 0) := by rfl

-- divide_DIVUW_0_1_7
example (s : riscv_state) : «dfn'DIVUW» (7,1,2) (fixture s 0 17 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 0) := by rfl

-- divide_DIVUW_0_2_0
example (s : riscv_state) : «dfn'DIVUW» (0,1,2) (fixture s 0 18446744073709551615 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 0) := by rfl

-- divide_DIVUW_0_2_1
example (s : riscv_state) : «dfn'DIVUW» (1,1,2) (fixture s 0 18446744073709551615 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 0) := by rfl

-- divide_DIVUW_0_2_2
example (s : riscv_state) : «dfn'DIVUW» (2,1,2) (fixture s 0 18446744073709551615 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 0) := by rfl

-- divide_DIVUW_0_2_7
example (s : riscv_state) : «dfn'DIVUW» (7,1,2) (fixture s 0 18446744073709551615 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 0) := by rfl

-- divide_DIVUW_0_3_0
example (s : riscv_state) : «dfn'DIVUW» (0,1,2) (fixture s 0 17 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 3) := by rfl

-- divide_DIVUW_0_3_1
example (s : riscv_state) : «dfn'DIVUW» (1,1,2) (fixture s 0 17 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 3) := by rfl

-- divide_DIVUW_0_3_2
example (s : riscv_state) : «dfn'DIVUW» (2,1,2) (fixture s 0 17 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 3) := by rfl

-- divide_DIVUW_0_3_7
example (s : riscv_state) : «dfn'DIVUW» (7,1,2) (fixture s 0 17 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 3) := by rfl

-- divide_DIVUW_0_4_0
example (s : riscv_state) : «dfn'DIVUW» (0,1,2) (fixture s 0 18446744073709551599 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551599 3) := by rfl

-- divide_DIVUW_0_4_1
example (s : riscv_state) : «dfn'DIVUW» (1,1,2) (fixture s 0 18446744073709551599 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551599 3) := by rfl

-- divide_DIVUW_0_4_2
example (s : riscv_state) : «dfn'DIVUW» (2,1,2) (fixture s 0 18446744073709551599 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551599 3) := by rfl

-- divide_DIVUW_0_4_7
example (s : riscv_state) : «dfn'DIVUW» (7,1,2) (fixture s 0 18446744073709551599 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551599 3) := by rfl

-- divide_DIVUW_0_5_0
example (s : riscv_state) : «dfn'DIVUW» (0,1,2) (fixture s 0 17 18446744073709551613) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 18446744073709551613) := by rfl

-- divide_DIVUW_0_5_1
example (s : riscv_state) : «dfn'DIVUW» (1,1,2) (fixture s 0 17 18446744073709551613) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 18446744073709551613) := by rfl

-- divide_DIVUW_0_5_2
example (s : riscv_state) : «dfn'DIVUW» (2,1,2) (fixture s 0 17 18446744073709551613) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 18446744073709551613) := by rfl

-- divide_DIVUW_0_5_7
example (s : riscv_state) : «dfn'DIVUW» (7,1,2) (fixture s 0 17 18446744073709551613) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 18446744073709551613) := by rfl

-- divide_DIVUW_0_6_0
example (s : riscv_state) : «dfn'DIVUW» (0,1,2) (fixture s 0 18446744073709551599 18446744073709551613) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551599 18446744073709551613) := by rfl

-- divide_DIVUW_0_6_1
example (s : riscv_state) : «dfn'DIVUW» (1,1,2) (fixture s 0 18446744073709551599 18446744073709551613) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551599 18446744073709551613) := by rfl

-- divide_DIVUW_0_6_2
example (s : riscv_state) : «dfn'DIVUW» (2,1,2) (fixture s 0 18446744073709551599 18446744073709551613) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551599 18446744073709551613) := by rfl

-- divide_DIVUW_0_6_7
example (s : riscv_state) : «dfn'DIVUW» (7,1,2) (fixture s 0 18446744073709551599 18446744073709551613) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551599 18446744073709551613) := by rfl

-- divide_DIVUW_0_7_0
example (s : riscv_state) : «dfn'DIVUW» (0,1,2) (fixture s 0 9223372036854775808 18446744073709551615) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775808 18446744073709551615) := by rfl

-- divide_DIVUW_0_7_1
example (s : riscv_state) : «dfn'DIVUW» (1,1,2) (fixture s 0 9223372036854775808 18446744073709551615) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775808 18446744073709551615) := by rfl

-- divide_DIVUW_0_7_2
example (s : riscv_state) : «dfn'DIVUW» (2,1,2) (fixture s 0 9223372036854775808 18446744073709551615) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775808 18446744073709551615) := by rfl

-- divide_DIVUW_0_7_7
example (s : riscv_state) : «dfn'DIVUW» (7,1,2) (fixture s 0 9223372036854775808 18446744073709551615) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775808 18446744073709551615) := by rfl

-- divide_DIVUW_0_8_0
example (s : riscv_state) : «dfn'DIVUW» (0,1,2) (fixture s 0 2147483648 4294967295) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483648 4294967295) := by rfl

-- divide_DIVUW_0_8_1
example (s : riscv_state) : «dfn'DIVUW» (1,1,2) (fixture s 0 2147483648 4294967295) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483648 4294967295) := by rfl

-- divide_DIVUW_0_8_2
example (s : riscv_state) : «dfn'DIVUW» (2,1,2) (fixture s 0 2147483648 4294967295) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483648 4294967295) := by rfl

-- divide_DIVUW_0_8_7
example (s : riscv_state) : «dfn'DIVUW» (7,1,2) (fixture s 0 2147483648 4294967295) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483648 4294967295) := by rfl

-- divide_DIVUW_0_9_0
example (s : riscv_state) : «dfn'DIVUW» (0,1,2) (fixture s 0 4294967313 4294967296) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967313 4294967296) := by rfl

-- divide_DIVUW_0_9_1
example (s : riscv_state) : «dfn'DIVUW» (1,1,2) (fixture s 0 4294967313 4294967296) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967313 4294967296) := by rfl

-- divide_DIVUW_0_9_2
example (s : riscv_state) : «dfn'DIVUW» (2,1,2) (fixture s 0 4294967313 4294967296) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967313 4294967296) := by rfl

-- divide_DIVUW_0_9_7
example (s : riscv_state) : «dfn'DIVUW» (7,1,2) (fixture s 0 4294967313 4294967296) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967313 4294967296) := by rfl

-- divide_DIVUW_0_10_0
example (s : riscv_state) : «dfn'DIVUW» (0,1,2) (fixture s 0 18446744073709551615 2) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 2) := by rfl

-- divide_DIVUW_0_10_1
example (s : riscv_state) : «dfn'DIVUW» (1,1,2) (fixture s 0 18446744073709551615 2) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 2) := by rfl

-- divide_DIVUW_0_10_2
example (s : riscv_state) : «dfn'DIVUW» (2,1,2) (fixture s 0 18446744073709551615 2) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 2) := by rfl

-- divide_DIVUW_0_10_7
example (s : riscv_state) : «dfn'DIVUW» (7,1,2) (fixture s 0 18446744073709551615 2) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 2) := by rfl

-- divide_DIVUW_0_11_0
example (s : riscv_state) : «dfn'DIVUW» (0,1,2) (fixture s 0 18446744073709551615 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 3) := by rfl

-- divide_DIVUW_0_11_1
example (s : riscv_state) : «dfn'DIVUW» (1,1,2) (fixture s 0 18446744073709551615 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 3) := by rfl

-- divide_DIVUW_0_11_2
example (s : riscv_state) : «dfn'DIVUW» (2,1,2) (fixture s 0 18446744073709551615 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 3) := by rfl

-- divide_DIVUW_0_11_7
example (s : riscv_state) : «dfn'DIVUW» (7,1,2) (fixture s 0 18446744073709551615 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 3) := by rfl

-- divide_DIVUW_0_12_0
example (s : riscv_state) : «dfn'DIVUW» (0,0,2) (fixture s 0 17 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 3) := by rfl

-- divide_DIVUW_0_12_1
example (s : riscv_state) : «dfn'DIVUW» (1,0,2) (fixture s 0 17 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 3) := by rfl

-- divide_DIVUW_0_12_2
example (s : riscv_state) : «dfn'DIVUW» (2,0,2) (fixture s 0 17 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 3) := by rfl

-- divide_DIVUW_0_12_7
example (s : riscv_state) : «dfn'DIVUW» (7,0,2) (fixture s 0 17 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 3) := by rfl

-- divide_DIVUW_0_13_0
example (s : riscv_state) : «dfn'DIVUW» (0,1,0) (fixture s 0 18446744073709551615 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 3) := by rfl

-- divide_DIVUW_0_13_1
example (s : riscv_state) : «dfn'DIVUW» (1,1,0) (fixture s 0 18446744073709551615 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 3) := by rfl

-- divide_DIVUW_0_13_2
example (s : riscv_state) : «dfn'DIVUW» (2,1,0) (fixture s 0 18446744073709551615 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 3) := by rfl

-- divide_DIVUW_0_13_7
example (s : riscv_state) : «dfn'DIVUW» (7,1,0) (fixture s 0 18446744073709551615 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 3) := by rfl

-- divide_DIVUW_0_14_0
example (s : riscv_state) : «dfn'DIVUW» (0,1,1) (fixture s 0 9223372036854775808 2) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775808 2) := by rfl

-- divide_DIVUW_0_14_1
example (s : riscv_state) : «dfn'DIVUW» (1,1,1) (fixture s 0 9223372036854775808 2) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775808 2) := by rfl

-- divide_DIVUW_0_14_2
example (s : riscv_state) : «dfn'DIVUW» (2,1,1) (fixture s 0 9223372036854775808 2) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775808 2) := by rfl

-- divide_DIVUW_0_14_7
example (s : riscv_state) : «dfn'DIVUW» (7,1,1) (fixture s 0 9223372036854775808 2) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775808 2) := by rfl

-- divide_DIVUW_2_0_0
example (s : riscv_state) : «dfn'DIVUW» (0,1,2) (fixture s 2 0 0) = (let t := fixture s 2 0 0; t) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_0_1
example (s : riscv_state) : «dfn'DIVUW» (1,1,2) (fixture s 2 0 0) = (let t := fixture s 2 0 0; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_0_2
example (s : riscv_state) : «dfn'DIVUW» (2,1,2) (fixture s 2 0 0) = (let t := fixture s 2 0 0; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_0_7
example (s : riscv_state) : «dfn'DIVUW» (7,1,2) (fixture s 2 0 0) = (let t := fixture s 2 0 0; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_1_0
example (s : riscv_state) : «dfn'DIVUW» (0,1,2) (fixture s 2 17 0) = (let t := fixture s 2 17 0; t) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_1_1
example (s : riscv_state) : «dfn'DIVUW» (1,1,2) (fixture s 2 17 0) = (let t := fixture s 2 17 0; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_1_2
example (s : riscv_state) : «dfn'DIVUW» (2,1,2) (fixture s 2 17 0) = (let t := fixture s 2 17 0; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_1_7
example (s : riscv_state) : «dfn'DIVUW» (7,1,2) (fixture s 2 17 0) = (let t := fixture s 2 17 0; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_2_0
example (s : riscv_state) : «dfn'DIVUW» (0,1,2) (fixture s 2 18446744073709551615 0) = (let t := fixture s 2 18446744073709551615 0; t) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_2_1
example (s : riscv_state) : «dfn'DIVUW» (1,1,2) (fixture s 2 18446744073709551615 0) = (let t := fixture s 2 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_2_2
example (s : riscv_state) : «dfn'DIVUW» (2,1,2) (fixture s 2 18446744073709551615 0) = (let t := fixture s 2 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_2_7
example (s : riscv_state) : «dfn'DIVUW» (7,1,2) (fixture s 2 18446744073709551615 0) = (let t := fixture s 2 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_3_0
example (s : riscv_state) : «dfn'DIVUW» (0,1,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; t) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_3_1
example (s : riscv_state) : «dfn'DIVUW» (1,1,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; {t with c_gpr := holUpdate 7 (holUpdate 1 5 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_3_2
example (s : riscv_state) : «dfn'DIVUW» (2,1,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; {t with c_gpr := holUpdate 7 (holUpdate 2 5 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_3_7
example (s : riscv_state) : «dfn'DIVUW» (7,1,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; {t with c_gpr := holUpdate 7 (holUpdate 7 5 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_4_0
example (s : riscv_state) : «dfn'DIVUW» (0,1,2) (fixture s 2 18446744073709551599 3) = (let t := fixture s 2 18446744073709551599 3; t) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_4_1
example (s : riscv_state) : «dfn'DIVUW» (1,1,2) (fixture s 2 18446744073709551599 3) = (let t := fixture s 2 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 1 1431655759 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_4_2
example (s : riscv_state) : «dfn'DIVUW» (2,1,2) (fixture s 2 18446744073709551599 3) = (let t := fixture s 2 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 2 1431655759 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_4_7
example (s : riscv_state) : «dfn'DIVUW» (7,1,2) (fixture s 2 18446744073709551599 3) = (let t := fixture s 2 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 7 1431655759 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_5_0
example (s : riscv_state) : «dfn'DIVUW» (0,1,2) (fixture s 2 17 18446744073709551613) = (let t := fixture s 2 17 18446744073709551613; t) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_5_1
example (s : riscv_state) : «dfn'DIVUW» (1,1,2) (fixture s 2 17 18446744073709551613) = (let t := fixture s 2 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_5_2
example (s : riscv_state) : «dfn'DIVUW» (2,1,2) (fixture s 2 17 18446744073709551613) = (let t := fixture s 2 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_5_7
example (s : riscv_state) : «dfn'DIVUW» (7,1,2) (fixture s 2 17 18446744073709551613) = (let t := fixture s 2 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_6_0
example (s : riscv_state) : «dfn'DIVUW» (0,1,2) (fixture s 2 18446744073709551599 18446744073709551613) = (let t := fixture s 2 18446744073709551599 18446744073709551613; t) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_6_1
example (s : riscv_state) : «dfn'DIVUW» (1,1,2) (fixture s 2 18446744073709551599 18446744073709551613) = (let t := fixture s 2 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_6_2
example (s : riscv_state) : «dfn'DIVUW» (2,1,2) (fixture s 2 18446744073709551599 18446744073709551613) = (let t := fixture s 2 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_6_7
example (s : riscv_state) : «dfn'DIVUW» (7,1,2) (fixture s 2 18446744073709551599 18446744073709551613) = (let t := fixture s 2 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_7_0
example (s : riscv_state) : «dfn'DIVUW» (0,1,2) (fixture s 2 9223372036854775808 18446744073709551615) = (let t := fixture s 2 9223372036854775808 18446744073709551615; t) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_7_1
example (s : riscv_state) : «dfn'DIVUW» (1,1,2) (fixture s 2 9223372036854775808 18446744073709551615) = (let t := fixture s 2 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_7_2
example (s : riscv_state) : «dfn'DIVUW» (2,1,2) (fixture s 2 9223372036854775808 18446744073709551615) = (let t := fixture s 2 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_7_7
example (s : riscv_state) : «dfn'DIVUW» (7,1,2) (fixture s 2 9223372036854775808 18446744073709551615) = (let t := fixture s 2 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_8_0
example (s : riscv_state) : «dfn'DIVUW» (0,1,2) (fixture s 2 2147483648 4294967295) = (let t := fixture s 2 2147483648 4294967295; t) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_8_1
example (s : riscv_state) : «dfn'DIVUW» (1,1,2) (fixture s 2 2147483648 4294967295) = (let t := fixture s 2 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_8_2
example (s : riscv_state) : «dfn'DIVUW» (2,1,2) (fixture s 2 2147483648 4294967295) = (let t := fixture s 2 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_8_7
example (s : riscv_state) : «dfn'DIVUW» (7,1,2) (fixture s 2 2147483648 4294967295) = (let t := fixture s 2 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_9_0
example (s : riscv_state) : «dfn'DIVUW» (0,1,2) (fixture s 2 4294967313 4294967296) = (let t := fixture s 2 4294967313 4294967296; t) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_9_1
example (s : riscv_state) : «dfn'DIVUW» (1,1,2) (fixture s 2 4294967313 4294967296) = (let t := fixture s 2 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_9_2
example (s : riscv_state) : «dfn'DIVUW» (2,1,2) (fixture s 2 4294967313 4294967296) = (let t := fixture s 2 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_9_7
example (s : riscv_state) : «dfn'DIVUW» (7,1,2) (fixture s 2 4294967313 4294967296) = (let t := fixture s 2 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_10_0
example (s : riscv_state) : «dfn'DIVUW» (0,1,2) (fixture s 2 18446744073709551615 2) = (let t := fixture s 2 18446744073709551615 2; t) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_10_1
example (s : riscv_state) : «dfn'DIVUW» (1,1,2) (fixture s 2 18446744073709551615 2) = (let t := fixture s 2 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 1 2147483647 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_10_2
example (s : riscv_state) : «dfn'DIVUW» (2,1,2) (fixture s 2 18446744073709551615 2) = (let t := fixture s 2 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 2 2147483647 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_10_7
example (s : riscv_state) : «dfn'DIVUW» (7,1,2) (fixture s 2 18446744073709551615 2) = (let t := fixture s 2 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 7 2147483647 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_11_0
example (s : riscv_state) : «dfn'DIVUW» (0,1,2) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; t) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_11_1
example (s : riscv_state) : «dfn'DIVUW» (1,1,2) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 1 1431655765 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_11_2
example (s : riscv_state) : «dfn'DIVUW» (2,1,2) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 2 1431655765 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_11_7
example (s : riscv_state) : «dfn'DIVUW» (7,1,2) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 7 1431655765 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_12_0
example (s : riscv_state) : «dfn'DIVUW» (0,0,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; t) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_12_1
example (s : riscv_state) : «dfn'DIVUW» (1,0,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_12_2
example (s : riscv_state) : «dfn'DIVUW» (2,0,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_12_7
example (s : riscv_state) : «dfn'DIVUW» (7,0,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_13_0
example (s : riscv_state) : «dfn'DIVUW» (0,1,0) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; t) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_13_1
example (s : riscv_state) : «dfn'DIVUW» (1,1,0) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_13_2
example (s : riscv_state) : «dfn'DIVUW» (2,1,0) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_13_7
example (s : riscv_state) : «dfn'DIVUW» (7,1,0) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_14_0
example (s : riscv_state) : «dfn'DIVUW» (0,1,1) (fixture s 2 9223372036854775808 2) = (let t := fixture s 2 9223372036854775808 2; t) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_14_1
example (s : riscv_state) : «dfn'DIVUW» (1,1,1) (fixture s 2 9223372036854775808 2) = (let t := fixture s 2 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_14_2
example (s : riscv_state) : «dfn'DIVUW» (2,1,1) (fixture s 2 9223372036854775808 2) = (let t := fixture s 2 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_2_14_7
example (s : riscv_state) : «dfn'DIVUW» (7,1,1) (fixture s 2 9223372036854775808 2) = (let t := fixture s 2 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_0_0
example (s : riscv_state) : «dfn'DIVUW» (0,1,2) (fixture s 3 0 0) = (let t := fixture s 3 0 0; t) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_0_1
example (s : riscv_state) : «dfn'DIVUW» (1,1,2) (fixture s 3 0 0) = (let t := fixture s 3 0 0; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_0_2
example (s : riscv_state) : «dfn'DIVUW» (2,1,2) (fixture s 3 0 0) = (let t := fixture s 3 0 0; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_0_7
example (s : riscv_state) : «dfn'DIVUW» (7,1,2) (fixture s 3 0 0) = (let t := fixture s 3 0 0; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_1_0
example (s : riscv_state) : «dfn'DIVUW» (0,1,2) (fixture s 3 17 0) = (let t := fixture s 3 17 0; t) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_1_1
example (s : riscv_state) : «dfn'DIVUW» (1,1,2) (fixture s 3 17 0) = (let t := fixture s 3 17 0; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_1_2
example (s : riscv_state) : «dfn'DIVUW» (2,1,2) (fixture s 3 17 0) = (let t := fixture s 3 17 0; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_1_7
example (s : riscv_state) : «dfn'DIVUW» (7,1,2) (fixture s 3 17 0) = (let t := fixture s 3 17 0; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_2_0
example (s : riscv_state) : «dfn'DIVUW» (0,1,2) (fixture s 3 18446744073709551615 0) = (let t := fixture s 3 18446744073709551615 0; t) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_2_1
example (s : riscv_state) : «dfn'DIVUW» (1,1,2) (fixture s 3 18446744073709551615 0) = (let t := fixture s 3 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_2_2
example (s : riscv_state) : «dfn'DIVUW» (2,1,2) (fixture s 3 18446744073709551615 0) = (let t := fixture s 3 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_2_7
example (s : riscv_state) : «dfn'DIVUW» (7,1,2) (fixture s 3 18446744073709551615 0) = (let t := fixture s 3 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_3_0
example (s : riscv_state) : «dfn'DIVUW» (0,1,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; t) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_3_1
example (s : riscv_state) : «dfn'DIVUW» (1,1,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; {t with c_gpr := holUpdate 7 (holUpdate 1 5 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_3_2
example (s : riscv_state) : «dfn'DIVUW» (2,1,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; {t with c_gpr := holUpdate 7 (holUpdate 2 5 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_3_7
example (s : riscv_state) : «dfn'DIVUW» (7,1,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; {t with c_gpr := holUpdate 7 (holUpdate 7 5 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_4_0
example (s : riscv_state) : «dfn'DIVUW» (0,1,2) (fixture s 3 18446744073709551599 3) = (let t := fixture s 3 18446744073709551599 3; t) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_4_1
example (s : riscv_state) : «dfn'DIVUW» (1,1,2) (fixture s 3 18446744073709551599 3) = (let t := fixture s 3 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 1 1431655759 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_4_2
example (s : riscv_state) : «dfn'DIVUW» (2,1,2) (fixture s 3 18446744073709551599 3) = (let t := fixture s 3 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 2 1431655759 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_4_7
example (s : riscv_state) : «dfn'DIVUW» (7,1,2) (fixture s 3 18446744073709551599 3) = (let t := fixture s 3 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 7 1431655759 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_5_0
example (s : riscv_state) : «dfn'DIVUW» (0,1,2) (fixture s 3 17 18446744073709551613) = (let t := fixture s 3 17 18446744073709551613; t) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_5_1
example (s : riscv_state) : «dfn'DIVUW» (1,1,2) (fixture s 3 17 18446744073709551613) = (let t := fixture s 3 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_5_2
example (s : riscv_state) : «dfn'DIVUW» (2,1,2) (fixture s 3 17 18446744073709551613) = (let t := fixture s 3 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_5_7
example (s : riscv_state) : «dfn'DIVUW» (7,1,2) (fixture s 3 17 18446744073709551613) = (let t := fixture s 3 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_6_0
example (s : riscv_state) : «dfn'DIVUW» (0,1,2) (fixture s 3 18446744073709551599 18446744073709551613) = (let t := fixture s 3 18446744073709551599 18446744073709551613; t) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_6_1
example (s : riscv_state) : «dfn'DIVUW» (1,1,2) (fixture s 3 18446744073709551599 18446744073709551613) = (let t := fixture s 3 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_6_2
example (s : riscv_state) : «dfn'DIVUW» (2,1,2) (fixture s 3 18446744073709551599 18446744073709551613) = (let t := fixture s 3 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_6_7
example (s : riscv_state) : «dfn'DIVUW» (7,1,2) (fixture s 3 18446744073709551599 18446744073709551613) = (let t := fixture s 3 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_7_0
example (s : riscv_state) : «dfn'DIVUW» (0,1,2) (fixture s 3 9223372036854775808 18446744073709551615) = (let t := fixture s 3 9223372036854775808 18446744073709551615; t) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_7_1
example (s : riscv_state) : «dfn'DIVUW» (1,1,2) (fixture s 3 9223372036854775808 18446744073709551615) = (let t := fixture s 3 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_7_2
example (s : riscv_state) : «dfn'DIVUW» (2,1,2) (fixture s 3 9223372036854775808 18446744073709551615) = (let t := fixture s 3 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_7_7
example (s : riscv_state) : «dfn'DIVUW» (7,1,2) (fixture s 3 9223372036854775808 18446744073709551615) = (let t := fixture s 3 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_8_0
example (s : riscv_state) : «dfn'DIVUW» (0,1,2) (fixture s 3 2147483648 4294967295) = (let t := fixture s 3 2147483648 4294967295; t) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_8_1
example (s : riscv_state) : «dfn'DIVUW» (1,1,2) (fixture s 3 2147483648 4294967295) = (let t := fixture s 3 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_8_2
example (s : riscv_state) : «dfn'DIVUW» (2,1,2) (fixture s 3 2147483648 4294967295) = (let t := fixture s 3 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_8_7
example (s : riscv_state) : «dfn'DIVUW» (7,1,2) (fixture s 3 2147483648 4294967295) = (let t := fixture s 3 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_9_0
example (s : riscv_state) : «dfn'DIVUW» (0,1,2) (fixture s 3 4294967313 4294967296) = (let t := fixture s 3 4294967313 4294967296; t) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_9_1
example (s : riscv_state) : «dfn'DIVUW» (1,1,2) (fixture s 3 4294967313 4294967296) = (let t := fixture s 3 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_9_2
example (s : riscv_state) : «dfn'DIVUW» (2,1,2) (fixture s 3 4294967313 4294967296) = (let t := fixture s 3 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_9_7
example (s : riscv_state) : «dfn'DIVUW» (7,1,2) (fixture s 3 4294967313 4294967296) = (let t := fixture s 3 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_10_0
example (s : riscv_state) : «dfn'DIVUW» (0,1,2) (fixture s 3 18446744073709551615 2) = (let t := fixture s 3 18446744073709551615 2; t) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_10_1
example (s : riscv_state) : «dfn'DIVUW» (1,1,2) (fixture s 3 18446744073709551615 2) = (let t := fixture s 3 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 1 2147483647 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_10_2
example (s : riscv_state) : «dfn'DIVUW» (2,1,2) (fixture s 3 18446744073709551615 2) = (let t := fixture s 3 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 2 2147483647 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_10_7
example (s : riscv_state) : «dfn'DIVUW» (7,1,2) (fixture s 3 18446744073709551615 2) = (let t := fixture s 3 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 7 2147483647 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_11_0
example (s : riscv_state) : «dfn'DIVUW» (0,1,2) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; t) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_11_1
example (s : riscv_state) : «dfn'DIVUW» (1,1,2) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 1 1431655765 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_11_2
example (s : riscv_state) : «dfn'DIVUW» (2,1,2) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 2 1431655765 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_11_7
example (s : riscv_state) : «dfn'DIVUW» (7,1,2) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 7 1431655765 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_12_0
example (s : riscv_state) : «dfn'DIVUW» (0,0,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; t) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_12_1
example (s : riscv_state) : «dfn'DIVUW» (1,0,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_12_2
example (s : riscv_state) : «dfn'DIVUW» (2,0,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_12_7
example (s : riscv_state) : «dfn'DIVUW» (7,0,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_13_0
example (s : riscv_state) : «dfn'DIVUW» (0,1,0) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; t) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_13_1
example (s : riscv_state) : «dfn'DIVUW» (1,1,0) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_13_2
example (s : riscv_state) : «dfn'DIVUW» (2,1,0) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_13_7
example (s : riscv_state) : «dfn'DIVUW» (7,1,0) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_14_0
example (s : riscv_state) : «dfn'DIVUW» (0,1,1) (fixture s 3 9223372036854775808 2) = (let t := fixture s 3 9223372036854775808 2; t) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_14_1
example (s : riscv_state) : «dfn'DIVUW» (1,1,1) (fixture s 3 9223372036854775808 2) = (let t := fixture s 3 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_14_2
example (s : riscv_state) : «dfn'DIVUW» (2,1,1) (fixture s 3 9223372036854775808 2) = (let t := fixture s 3 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_DIVUW_3_14_7
example (s : riscv_state) : «dfn'DIVUW» (7,1,1) (fixture s 3 9223372036854775808 2) = (let t := fixture s 3 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'DIVUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_0_0_0
example (s : riscv_state) : «dfn'REMUW» (0,1,2) (fixture s 0 0 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 0 0) := by rfl

-- divide_REMUW_0_0_1
example (s : riscv_state) : «dfn'REMUW» (1,1,2) (fixture s 0 0 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 0 0) := by rfl

-- divide_REMUW_0_0_2
example (s : riscv_state) : «dfn'REMUW» (2,1,2) (fixture s 0 0 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 0 0) := by rfl

-- divide_REMUW_0_0_7
example (s : riscv_state) : «dfn'REMUW» (7,1,2) (fixture s 0 0 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 0 0) := by rfl

-- divide_REMUW_0_1_0
example (s : riscv_state) : «dfn'REMUW» (0,1,2) (fixture s 0 17 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 0) := by rfl

-- divide_REMUW_0_1_1
example (s : riscv_state) : «dfn'REMUW» (1,1,2) (fixture s 0 17 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 0) := by rfl

-- divide_REMUW_0_1_2
example (s : riscv_state) : «dfn'REMUW» (2,1,2) (fixture s 0 17 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 0) := by rfl

-- divide_REMUW_0_1_7
example (s : riscv_state) : «dfn'REMUW» (7,1,2) (fixture s 0 17 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 0) := by rfl

-- divide_REMUW_0_2_0
example (s : riscv_state) : «dfn'REMUW» (0,1,2) (fixture s 0 18446744073709551615 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 0) := by rfl

-- divide_REMUW_0_2_1
example (s : riscv_state) : «dfn'REMUW» (1,1,2) (fixture s 0 18446744073709551615 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 0) := by rfl

-- divide_REMUW_0_2_2
example (s : riscv_state) : «dfn'REMUW» (2,1,2) (fixture s 0 18446744073709551615 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 0) := by rfl

-- divide_REMUW_0_2_7
example (s : riscv_state) : «dfn'REMUW» (7,1,2) (fixture s 0 18446744073709551615 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 0) := by rfl

-- divide_REMUW_0_3_0
example (s : riscv_state) : «dfn'REMUW» (0,1,2) (fixture s 0 17 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 3) := by rfl

-- divide_REMUW_0_3_1
example (s : riscv_state) : «dfn'REMUW» (1,1,2) (fixture s 0 17 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 3) := by rfl

-- divide_REMUW_0_3_2
example (s : riscv_state) : «dfn'REMUW» (2,1,2) (fixture s 0 17 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 3) := by rfl

-- divide_REMUW_0_3_7
example (s : riscv_state) : «dfn'REMUW» (7,1,2) (fixture s 0 17 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 3) := by rfl

-- divide_REMUW_0_4_0
example (s : riscv_state) : «dfn'REMUW» (0,1,2) (fixture s 0 18446744073709551599 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551599 3) := by rfl

-- divide_REMUW_0_4_1
example (s : riscv_state) : «dfn'REMUW» (1,1,2) (fixture s 0 18446744073709551599 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551599 3) := by rfl

-- divide_REMUW_0_4_2
example (s : riscv_state) : «dfn'REMUW» (2,1,2) (fixture s 0 18446744073709551599 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551599 3) := by rfl

-- divide_REMUW_0_4_7
example (s : riscv_state) : «dfn'REMUW» (7,1,2) (fixture s 0 18446744073709551599 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551599 3) := by rfl

-- divide_REMUW_0_5_0
example (s : riscv_state) : «dfn'REMUW» (0,1,2) (fixture s 0 17 18446744073709551613) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 18446744073709551613) := by rfl

-- divide_REMUW_0_5_1
example (s : riscv_state) : «dfn'REMUW» (1,1,2) (fixture s 0 17 18446744073709551613) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 18446744073709551613) := by rfl

-- divide_REMUW_0_5_2
example (s : riscv_state) : «dfn'REMUW» (2,1,2) (fixture s 0 17 18446744073709551613) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 18446744073709551613) := by rfl

-- divide_REMUW_0_5_7
example (s : riscv_state) : «dfn'REMUW» (7,1,2) (fixture s 0 17 18446744073709551613) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 18446744073709551613) := by rfl

-- divide_REMUW_0_6_0
example (s : riscv_state) : «dfn'REMUW» (0,1,2) (fixture s 0 18446744073709551599 18446744073709551613) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551599 18446744073709551613) := by rfl

-- divide_REMUW_0_6_1
example (s : riscv_state) : «dfn'REMUW» (1,1,2) (fixture s 0 18446744073709551599 18446744073709551613) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551599 18446744073709551613) := by rfl

-- divide_REMUW_0_6_2
example (s : riscv_state) : «dfn'REMUW» (2,1,2) (fixture s 0 18446744073709551599 18446744073709551613) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551599 18446744073709551613) := by rfl

-- divide_REMUW_0_6_7
example (s : riscv_state) : «dfn'REMUW» (7,1,2) (fixture s 0 18446744073709551599 18446744073709551613) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551599 18446744073709551613) := by rfl

-- divide_REMUW_0_7_0
example (s : riscv_state) : «dfn'REMUW» (0,1,2) (fixture s 0 9223372036854775808 18446744073709551615) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775808 18446744073709551615) := by rfl

-- divide_REMUW_0_7_1
example (s : riscv_state) : «dfn'REMUW» (1,1,2) (fixture s 0 9223372036854775808 18446744073709551615) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775808 18446744073709551615) := by rfl

-- divide_REMUW_0_7_2
example (s : riscv_state) : «dfn'REMUW» (2,1,2) (fixture s 0 9223372036854775808 18446744073709551615) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775808 18446744073709551615) := by rfl

-- divide_REMUW_0_7_7
example (s : riscv_state) : «dfn'REMUW» (7,1,2) (fixture s 0 9223372036854775808 18446744073709551615) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775808 18446744073709551615) := by rfl

-- divide_REMUW_0_8_0
example (s : riscv_state) : «dfn'REMUW» (0,1,2) (fixture s 0 2147483648 4294967295) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483648 4294967295) := by rfl

-- divide_REMUW_0_8_1
example (s : riscv_state) : «dfn'REMUW» (1,1,2) (fixture s 0 2147483648 4294967295) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483648 4294967295) := by rfl

-- divide_REMUW_0_8_2
example (s : riscv_state) : «dfn'REMUW» (2,1,2) (fixture s 0 2147483648 4294967295) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483648 4294967295) := by rfl

-- divide_REMUW_0_8_7
example (s : riscv_state) : «dfn'REMUW» (7,1,2) (fixture s 0 2147483648 4294967295) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483648 4294967295) := by rfl

-- divide_REMUW_0_9_0
example (s : riscv_state) : «dfn'REMUW» (0,1,2) (fixture s 0 4294967313 4294967296) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967313 4294967296) := by rfl

-- divide_REMUW_0_9_1
example (s : riscv_state) : «dfn'REMUW» (1,1,2) (fixture s 0 4294967313 4294967296) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967313 4294967296) := by rfl

-- divide_REMUW_0_9_2
example (s : riscv_state) : «dfn'REMUW» (2,1,2) (fixture s 0 4294967313 4294967296) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967313 4294967296) := by rfl

-- divide_REMUW_0_9_7
example (s : riscv_state) : «dfn'REMUW» (7,1,2) (fixture s 0 4294967313 4294967296) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967313 4294967296) := by rfl

-- divide_REMUW_0_10_0
example (s : riscv_state) : «dfn'REMUW» (0,1,2) (fixture s 0 18446744073709551615 2) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 2) := by rfl

-- divide_REMUW_0_10_1
example (s : riscv_state) : «dfn'REMUW» (1,1,2) (fixture s 0 18446744073709551615 2) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 2) := by rfl

-- divide_REMUW_0_10_2
example (s : riscv_state) : «dfn'REMUW» (2,1,2) (fixture s 0 18446744073709551615 2) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 2) := by rfl

-- divide_REMUW_0_10_7
example (s : riscv_state) : «dfn'REMUW» (7,1,2) (fixture s 0 18446744073709551615 2) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 2) := by rfl

-- divide_REMUW_0_11_0
example (s : riscv_state) : «dfn'REMUW» (0,1,2) (fixture s 0 18446744073709551615 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 3) := by rfl

-- divide_REMUW_0_11_1
example (s : riscv_state) : «dfn'REMUW» (1,1,2) (fixture s 0 18446744073709551615 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 3) := by rfl

-- divide_REMUW_0_11_2
example (s : riscv_state) : «dfn'REMUW» (2,1,2) (fixture s 0 18446744073709551615 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 3) := by rfl

-- divide_REMUW_0_11_7
example (s : riscv_state) : «dfn'REMUW» (7,1,2) (fixture s 0 18446744073709551615 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 3) := by rfl

-- divide_REMUW_0_12_0
example (s : riscv_state) : «dfn'REMUW» (0,0,2) (fixture s 0 17 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 3) := by rfl

-- divide_REMUW_0_12_1
example (s : riscv_state) : «dfn'REMUW» (1,0,2) (fixture s 0 17 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 3) := by rfl

-- divide_REMUW_0_12_2
example (s : riscv_state) : «dfn'REMUW» (2,0,2) (fixture s 0 17 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 3) := by rfl

-- divide_REMUW_0_12_7
example (s : riscv_state) : «dfn'REMUW» (7,0,2) (fixture s 0 17 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 3) := by rfl

-- divide_REMUW_0_13_0
example (s : riscv_state) : «dfn'REMUW» (0,1,0) (fixture s 0 18446744073709551615 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 3) := by rfl

-- divide_REMUW_0_13_1
example (s : riscv_state) : «dfn'REMUW» (1,1,0) (fixture s 0 18446744073709551615 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 3) := by rfl

-- divide_REMUW_0_13_2
example (s : riscv_state) : «dfn'REMUW» (2,1,0) (fixture s 0 18446744073709551615 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 3) := by rfl

-- divide_REMUW_0_13_7
example (s : riscv_state) : «dfn'REMUW» (7,1,0) (fixture s 0 18446744073709551615 3) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 3) := by rfl

-- divide_REMUW_0_14_0
example (s : riscv_state) : «dfn'REMUW» (0,1,1) (fixture s 0 9223372036854775808 2) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775808 2) := by rfl

-- divide_REMUW_0_14_1
example (s : riscv_state) : «dfn'REMUW» (1,1,1) (fixture s 0 9223372036854775808 2) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775808 2) := by rfl

-- divide_REMUW_0_14_2
example (s : riscv_state) : «dfn'REMUW» (2,1,1) (fixture s 0 9223372036854775808 2) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775808 2) := by rfl

-- divide_REMUW_0_14_7
example (s : riscv_state) : «dfn'REMUW» (7,1,1) (fixture s 0 9223372036854775808 2) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775808 2) := by rfl

-- divide_REMUW_2_0_0
example (s : riscv_state) : «dfn'REMUW» (0,1,2) (fixture s 2 0 0) = (let t := fixture s 2 0 0; t) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_0_1
example (s : riscv_state) : «dfn'REMUW» (1,1,2) (fixture s 2 0 0) = (let t := fixture s 2 0 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_0_2
example (s : riscv_state) : «dfn'REMUW» (2,1,2) (fixture s 2 0 0) = (let t := fixture s 2 0 0; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_0_7
example (s : riscv_state) : «dfn'REMUW» (7,1,2) (fixture s 2 0 0) = (let t := fixture s 2 0 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_1_0
example (s : riscv_state) : «dfn'REMUW» (0,1,2) (fixture s 2 17 0) = (let t := fixture s 2 17 0; t) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_1_1
example (s : riscv_state) : «dfn'REMUW» (1,1,2) (fixture s 2 17 0) = (let t := fixture s 2 17 0; {t with c_gpr := holUpdate 7 (holUpdate 1 17 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_1_2
example (s : riscv_state) : «dfn'REMUW» (2,1,2) (fixture s 2 17 0) = (let t := fixture s 2 17 0; {t with c_gpr := holUpdate 7 (holUpdate 2 17 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_1_7
example (s : riscv_state) : «dfn'REMUW» (7,1,2) (fixture s 2 17 0) = (let t := fixture s 2 17 0; {t with c_gpr := holUpdate 7 (holUpdate 7 17 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_2_0
example (s : riscv_state) : «dfn'REMUW» (0,1,2) (fixture s 2 18446744073709551615 0) = (let t := fixture s 2 18446744073709551615 0; t) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_2_1
example (s : riscv_state) : «dfn'REMUW» (1,1,2) (fixture s 2 18446744073709551615 0) = (let t := fixture s 2 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_2_2
example (s : riscv_state) : «dfn'REMUW» (2,1,2) (fixture s 2 18446744073709551615 0) = (let t := fixture s 2 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_2_7
example (s : riscv_state) : «dfn'REMUW» (7,1,2) (fixture s 2 18446744073709551615 0) = (let t := fixture s 2 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_3_0
example (s : riscv_state) : «dfn'REMUW» (0,1,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; t) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_3_1
example (s : riscv_state) : «dfn'REMUW» (1,1,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; {t with c_gpr := holUpdate 7 (holUpdate 1 2 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_3_2
example (s : riscv_state) : «dfn'REMUW» (2,1,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; {t with c_gpr := holUpdate 7 (holUpdate 2 2 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_3_7
example (s : riscv_state) : «dfn'REMUW» (7,1,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; {t with c_gpr := holUpdate 7 (holUpdate 7 2 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_4_0
example (s : riscv_state) : «dfn'REMUW» (0,1,2) (fixture s 2 18446744073709551599 3) = (let t := fixture s 2 18446744073709551599 3; t) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_4_1
example (s : riscv_state) : «dfn'REMUW» (1,1,2) (fixture s 2 18446744073709551599 3) = (let t := fixture s 2 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 1 2 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_4_2
example (s : riscv_state) : «dfn'REMUW» (2,1,2) (fixture s 2 18446744073709551599 3) = (let t := fixture s 2 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 2 2 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_4_7
example (s : riscv_state) : «dfn'REMUW» (7,1,2) (fixture s 2 18446744073709551599 3) = (let t := fixture s 2 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 7 2 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_5_0
example (s : riscv_state) : «dfn'REMUW» (0,1,2) (fixture s 2 17 18446744073709551613) = (let t := fixture s 2 17 18446744073709551613; t) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_5_1
example (s : riscv_state) : «dfn'REMUW» (1,1,2) (fixture s 2 17 18446744073709551613) = (let t := fixture s 2 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 1 17 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_5_2
example (s : riscv_state) : «dfn'REMUW» (2,1,2) (fixture s 2 17 18446744073709551613) = (let t := fixture s 2 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 2 17 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_5_7
example (s : riscv_state) : «dfn'REMUW» (7,1,2) (fixture s 2 17 18446744073709551613) = (let t := fixture s 2 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 7 17 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_6_0
example (s : riscv_state) : «dfn'REMUW» (0,1,2) (fixture s 2 18446744073709551599 18446744073709551613) = (let t := fixture s 2 18446744073709551599 18446744073709551613; t) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_6_1
example (s : riscv_state) : «dfn'REMUW» (1,1,2) (fixture s 2 18446744073709551599 18446744073709551613) = (let t := fixture s 2 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551599 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_6_2
example (s : riscv_state) : «dfn'REMUW» (2,1,2) (fixture s 2 18446744073709551599 18446744073709551613) = (let t := fixture s 2 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551599 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_6_7
example (s : riscv_state) : «dfn'REMUW» (7,1,2) (fixture s 2 18446744073709551599 18446744073709551613) = (let t := fixture s 2 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551599 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_7_0
example (s : riscv_state) : «dfn'REMUW» (0,1,2) (fixture s 2 9223372036854775808 18446744073709551615) = (let t := fixture s 2 9223372036854775808 18446744073709551615; t) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_7_1
example (s : riscv_state) : «dfn'REMUW» (1,1,2) (fixture s 2 9223372036854775808 18446744073709551615) = (let t := fixture s 2 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_7_2
example (s : riscv_state) : «dfn'REMUW» (2,1,2) (fixture s 2 9223372036854775808 18446744073709551615) = (let t := fixture s 2 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_7_7
example (s : riscv_state) : «dfn'REMUW» (7,1,2) (fixture s 2 9223372036854775808 18446744073709551615) = (let t := fixture s 2 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_8_0
example (s : riscv_state) : «dfn'REMUW» (0,1,2) (fixture s 2 2147483648 4294967295) = (let t := fixture s 2 2147483648 4294967295; t) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_8_1
example (s : riscv_state) : «dfn'REMUW» (1,1,2) (fixture s 2 2147483648 4294967295) = (let t := fixture s 2 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_8_2
example (s : riscv_state) : «dfn'REMUW» (2,1,2) (fixture s 2 2147483648 4294967295) = (let t := fixture s 2 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_8_7
example (s : riscv_state) : «dfn'REMUW» (7,1,2) (fixture s 2 2147483648 4294967295) = (let t := fixture s 2 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_9_0
example (s : riscv_state) : «dfn'REMUW» (0,1,2) (fixture s 2 4294967313 4294967296) = (let t := fixture s 2 4294967313 4294967296; t) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_9_1
example (s : riscv_state) : «dfn'REMUW» (1,1,2) (fixture s 2 4294967313 4294967296) = (let t := fixture s 2 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 1 17 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_9_2
example (s : riscv_state) : «dfn'REMUW» (2,1,2) (fixture s 2 4294967313 4294967296) = (let t := fixture s 2 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 2 17 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_9_7
example (s : riscv_state) : «dfn'REMUW» (7,1,2) (fixture s 2 4294967313 4294967296) = (let t := fixture s 2 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 7 17 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_10_0
example (s : riscv_state) : «dfn'REMUW» (0,1,2) (fixture s 2 18446744073709551615 2) = (let t := fixture s 2 18446744073709551615 2; t) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_10_1
example (s : riscv_state) : «dfn'REMUW» (1,1,2) (fixture s 2 18446744073709551615 2) = (let t := fixture s 2 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_10_2
example (s : riscv_state) : «dfn'REMUW» (2,1,2) (fixture s 2 18446744073709551615 2) = (let t := fixture s 2 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_10_7
example (s : riscv_state) : «dfn'REMUW» (7,1,2) (fixture s 2 18446744073709551615 2) = (let t := fixture s 2 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_11_0
example (s : riscv_state) : «dfn'REMUW» (0,1,2) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; t) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_11_1
example (s : riscv_state) : «dfn'REMUW» (1,1,2) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_11_2
example (s : riscv_state) : «dfn'REMUW» (2,1,2) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_11_7
example (s : riscv_state) : «dfn'REMUW» (7,1,2) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_12_0
example (s : riscv_state) : «dfn'REMUW» (0,0,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; t) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_12_1
example (s : riscv_state) : «dfn'REMUW» (1,0,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_12_2
example (s : riscv_state) : «dfn'REMUW» (2,0,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_12_7
example (s : riscv_state) : «dfn'REMUW» (7,0,2) (fixture s 2 17 3) = (let t := fixture s 2 17 3; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_13_0
example (s : riscv_state) : «dfn'REMUW» (0,1,0) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; t) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_13_1
example (s : riscv_state) : «dfn'REMUW» (1,1,0) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_13_2
example (s : riscv_state) : «dfn'REMUW» (2,1,0) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_13_7
example (s : riscv_state) : «dfn'REMUW» (7,1,0) (fixture s 2 18446744073709551615 3) = (let t := fixture s 2 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_14_0
example (s : riscv_state) : «dfn'REMUW» (0,1,1) (fixture s 2 9223372036854775808 2) = (let t := fixture s 2 9223372036854775808 2; t) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_14_1
example (s : riscv_state) : «dfn'REMUW» (1,1,1) (fixture s 2 9223372036854775808 2) = (let t := fixture s 2 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_14_2
example (s : riscv_state) : «dfn'REMUW» (2,1,1) (fixture s 2 9223372036854775808 2) = (let t := fixture s 2 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_2_14_7
example (s : riscv_state) : «dfn'REMUW» (7,1,1) (fixture s 2 9223372036854775808 2) = (let t := fixture s 2 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_0_0
example (s : riscv_state) : «dfn'REMUW» (0,1,2) (fixture s 3 0 0) = (let t := fixture s 3 0 0; t) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_0_1
example (s : riscv_state) : «dfn'REMUW» (1,1,2) (fixture s 3 0 0) = (let t := fixture s 3 0 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_0_2
example (s : riscv_state) : «dfn'REMUW» (2,1,2) (fixture s 3 0 0) = (let t := fixture s 3 0 0; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_0_7
example (s : riscv_state) : «dfn'REMUW» (7,1,2) (fixture s 3 0 0) = (let t := fixture s 3 0 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_1_0
example (s : riscv_state) : «dfn'REMUW» (0,1,2) (fixture s 3 17 0) = (let t := fixture s 3 17 0; t) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_1_1
example (s : riscv_state) : «dfn'REMUW» (1,1,2) (fixture s 3 17 0) = (let t := fixture s 3 17 0; {t with c_gpr := holUpdate 7 (holUpdate 1 17 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_1_2
example (s : riscv_state) : «dfn'REMUW» (2,1,2) (fixture s 3 17 0) = (let t := fixture s 3 17 0; {t with c_gpr := holUpdate 7 (holUpdate 2 17 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_1_7
example (s : riscv_state) : «dfn'REMUW» (7,1,2) (fixture s 3 17 0) = (let t := fixture s 3 17 0; {t with c_gpr := holUpdate 7 (holUpdate 7 17 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_2_0
example (s : riscv_state) : «dfn'REMUW» (0,1,2) (fixture s 3 18446744073709551615 0) = (let t := fixture s 3 18446744073709551615 0; t) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_2_1
example (s : riscv_state) : «dfn'REMUW» (1,1,2) (fixture s 3 18446744073709551615 0) = (let t := fixture s 3 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_2_2
example (s : riscv_state) : «dfn'REMUW» (2,1,2) (fixture s 3 18446744073709551615 0) = (let t := fixture s 3 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_2_7
example (s : riscv_state) : «dfn'REMUW» (7,1,2) (fixture s 3 18446744073709551615 0) = (let t := fixture s 3 18446744073709551615 0; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_3_0
example (s : riscv_state) : «dfn'REMUW» (0,1,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; t) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_3_1
example (s : riscv_state) : «dfn'REMUW» (1,1,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; {t with c_gpr := holUpdate 7 (holUpdate 1 2 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_3_2
example (s : riscv_state) : «dfn'REMUW» (2,1,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; {t with c_gpr := holUpdate 7 (holUpdate 2 2 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_3_7
example (s : riscv_state) : «dfn'REMUW» (7,1,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; {t with c_gpr := holUpdate 7 (holUpdate 7 2 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_4_0
example (s : riscv_state) : «dfn'REMUW» (0,1,2) (fixture s 3 18446744073709551599 3) = (let t := fixture s 3 18446744073709551599 3; t) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_4_1
example (s : riscv_state) : «dfn'REMUW» (1,1,2) (fixture s 3 18446744073709551599 3) = (let t := fixture s 3 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 1 2 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_4_2
example (s : riscv_state) : «dfn'REMUW» (2,1,2) (fixture s 3 18446744073709551599 3) = (let t := fixture s 3 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 2 2 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_4_7
example (s : riscv_state) : «dfn'REMUW» (7,1,2) (fixture s 3 18446744073709551599 3) = (let t := fixture s 3 18446744073709551599 3; {t with c_gpr := holUpdate 7 (holUpdate 7 2 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_5_0
example (s : riscv_state) : «dfn'REMUW» (0,1,2) (fixture s 3 17 18446744073709551613) = (let t := fixture s 3 17 18446744073709551613; t) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_5_1
example (s : riscv_state) : «dfn'REMUW» (1,1,2) (fixture s 3 17 18446744073709551613) = (let t := fixture s 3 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 1 17 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_5_2
example (s : riscv_state) : «dfn'REMUW» (2,1,2) (fixture s 3 17 18446744073709551613) = (let t := fixture s 3 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 2 17 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_5_7
example (s : riscv_state) : «dfn'REMUW» (7,1,2) (fixture s 3 17 18446744073709551613) = (let t := fixture s 3 17 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 7 17 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_6_0
example (s : riscv_state) : «dfn'REMUW» (0,1,2) (fixture s 3 18446744073709551599 18446744073709551613) = (let t := fixture s 3 18446744073709551599 18446744073709551613; t) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_6_1
example (s : riscv_state) : «dfn'REMUW» (1,1,2) (fixture s 3 18446744073709551599 18446744073709551613) = (let t := fixture s 3 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551599 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_6_2
example (s : riscv_state) : «dfn'REMUW» (2,1,2) (fixture s 3 18446744073709551599 18446744073709551613) = (let t := fixture s 3 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551599 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_6_7
example (s : riscv_state) : «dfn'REMUW» (7,1,2) (fixture s 3 18446744073709551599 18446744073709551613) = (let t := fixture s 3 18446744073709551599 18446744073709551613; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551599 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_7_0
example (s : riscv_state) : «dfn'REMUW» (0,1,2) (fixture s 3 9223372036854775808 18446744073709551615) = (let t := fixture s 3 9223372036854775808 18446744073709551615; t) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_7_1
example (s : riscv_state) : «dfn'REMUW» (1,1,2) (fixture s 3 9223372036854775808 18446744073709551615) = (let t := fixture s 3 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_7_2
example (s : riscv_state) : «dfn'REMUW» (2,1,2) (fixture s 3 9223372036854775808 18446744073709551615) = (let t := fixture s 3 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_7_7
example (s : riscv_state) : «dfn'REMUW» (7,1,2) (fixture s 3 9223372036854775808 18446744073709551615) = (let t := fixture s 3 9223372036854775808 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_8_0
example (s : riscv_state) : «dfn'REMUW» (0,1,2) (fixture s 3 2147483648 4294967295) = (let t := fixture s 3 2147483648 4294967295; t) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_8_1
example (s : riscv_state) : «dfn'REMUW» (1,1,2) (fixture s 3 2147483648 4294967295) = (let t := fixture s 3 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_8_2
example (s : riscv_state) : «dfn'REMUW» (2,1,2) (fixture s 3 2147483648 4294967295) = (let t := fixture s 3 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_8_7
example (s : riscv_state) : «dfn'REMUW» (7,1,2) (fixture s 3 2147483648 4294967295) = (let t := fixture s 3 2147483648 4294967295; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_9_0
example (s : riscv_state) : «dfn'REMUW» (0,1,2) (fixture s 3 4294967313 4294967296) = (let t := fixture s 3 4294967313 4294967296; t) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_9_1
example (s : riscv_state) : «dfn'REMUW» (1,1,2) (fixture s 3 4294967313 4294967296) = (let t := fixture s 3 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 1 17 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_9_2
example (s : riscv_state) : «dfn'REMUW» (2,1,2) (fixture s 3 4294967313 4294967296) = (let t := fixture s 3 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 2 17 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_9_7
example (s : riscv_state) : «dfn'REMUW» (7,1,2) (fixture s 3 4294967313 4294967296) = (let t := fixture s 3 4294967313 4294967296; {t with c_gpr := holUpdate 7 (holUpdate 7 17 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_10_0
example (s : riscv_state) : «dfn'REMUW» (0,1,2) (fixture s 3 18446744073709551615 2) = (let t := fixture s 3 18446744073709551615 2; t) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_10_1
example (s : riscv_state) : «dfn'REMUW» (1,1,2) (fixture s 3 18446744073709551615 2) = (let t := fixture s 3 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 1 1 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_10_2
example (s : riscv_state) : «dfn'REMUW» (2,1,2) (fixture s 3 18446744073709551615 2) = (let t := fixture s 3 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 2 1 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_10_7
example (s : riscv_state) : «dfn'REMUW» (7,1,2) (fixture s 3 18446744073709551615 2) = (let t := fixture s 3 18446744073709551615 2; {t with c_gpr := holUpdate 7 (holUpdate 7 1 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_11_0
example (s : riscv_state) : «dfn'REMUW» (0,1,2) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; t) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_11_1
example (s : riscv_state) : «dfn'REMUW» (1,1,2) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_11_2
example (s : riscv_state) : «dfn'REMUW» (2,1,2) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_11_7
example (s : riscv_state) : «dfn'REMUW» (7,1,2) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_12_0
example (s : riscv_state) : «dfn'REMUW» (0,0,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; t) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_12_1
example (s : riscv_state) : «dfn'REMUW» (1,0,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_12_2
example (s : riscv_state) : «dfn'REMUW» (2,0,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_12_7
example (s : riscv_state) : «dfn'REMUW» (7,0,2) (fixture s 3 17 3) = (let t := fixture s 3 17 3; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_13_0
example (s : riscv_state) : «dfn'REMUW» (0,1,0) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; t) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_13_1
example (s : riscv_state) : «dfn'REMUW» (1,1,0) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_13_2
example (s : riscv_state) : «dfn'REMUW» (2,1,0) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_13_7
example (s : riscv_state) : «dfn'REMUW» (7,1,0) (fixture s 3 18446744073709551615 3) = (let t := fixture s 3 18446744073709551615 3; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709551615 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_14_0
example (s : riscv_state) : «dfn'REMUW» (0,1,1) (fixture s 3 9223372036854775808 2) = (let t := fixture s 3 9223372036854775808 2; t) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_14_1
example (s : riscv_state) : «dfn'REMUW» (1,1,1) (fixture s 3 9223372036854775808 2) = (let t := fixture s 3 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_14_2
example (s : riscv_state) : «dfn'REMUW» (2,1,1) (fixture s 3 9223372036854775808 2) = (let t := fixture s 3 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_REMUW_3_14_7
example (s : riscv_state) : «dfn'REMUW» (7,1,1) (fixture s 3 9223372036854775808 2) = (let t := fixture s 3 9223372036854775808 2; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
  simp [«dfn'REMUW», fixture, in32BitMode, curArch, architecture, MCSR, GPR, gpr]
  rfl

-- divide_symbolic_DIV_0
example (s : riscv_state) : «dfn'DIV» (0,0,0) ({fixture s 1 17 9 with exception := exception.NoException}) = ({fixture s 1 17 9 with exception := exception.NoException}) := by rfl

-- divide_symbolic_DIV_1
example (s : riscv_state) : «dfn'DIV» (0,0,0) ({fixture s 1 17 9 with exception := exception.UNDEFINED [9]}) = ({fixture s 1 17 9 with exception := exception.UNDEFINED [9]}) := by rfl

-- divide_symbolic_REM_0
example (s : riscv_state) : «dfn'REM» (0,0,0) ({fixture s 1 17 9 with exception := exception.NoException}) = ({fixture s 1 17 9 with exception := exception.NoException}) := by rfl

-- divide_symbolic_REM_1
example (s : riscv_state) : «dfn'REM» (0,0,0) ({fixture s 1 17 9 with exception := exception.UNDEFINED [9]}) = ({fixture s 1 17 9 with exception := exception.UNDEFINED [9]}) := by rfl

-- divide_symbolic_DIVU_0
example (s : riscv_state) : «dfn'DIVU» (0,0,0) ({fixture s 1 17 9 with exception := exception.NoException}) = (match in32BitMode () ({fixture s 1 17 9 with exception := exception.NoException}) with | (_,u) => match in32BitMode () u with | (_,u1) => u1) := by simp only [«dfn'DIVU», zeroWrite, ite_self]

-- divide_symbolic_DIVU_1
example (s : riscv_state) : «dfn'DIVU» (0,0,0) ({fixture s 1 17 9 with exception := exception.UNDEFINED [9]}) = (match in32BitMode () ({fixture s 1 17 9 with exception := exception.UNDEFINED [9]}) with | (_,u) => match in32BitMode () u with | (_,u1) => u1) := by simp only [«dfn'DIVU», zeroWrite, ite_self]

-- divide_symbolic_REMU_0
example (s : riscv_state) : «dfn'REMU» (0,0,0) ({fixture s 1 17 9 with exception := exception.NoException}) = ({fixture s 1 17 9 with exception := exception.NoException}) := by rfl

-- divide_symbolic_REMU_1
example (s : riscv_state) : «dfn'REMU» (0,0,0) ({fixture s 1 17 9 with exception := exception.UNDEFINED [9]}) = ({fixture s 1 17 9 with exception := exception.UNDEFINED [9]}) := by rfl

-- divide_symbolic_DIVW_0
example (s : riscv_state) : «dfn'DIVW» (0,0,0) ({fixture s 1 17 9 with exception := exception.NoException}) = (match in32BitMode () ({fixture s 1 17 9 with exception := exception.NoException}) with | (v,u) => if v then signalException ExceptionType.Illegal_Instr u else u) := by rfl

-- divide_symbolic_DIVW_1
example (s : riscv_state) : «dfn'DIVW» (0,0,0) ({fixture s 1 17 9 with exception := exception.UNDEFINED [9]}) = (match in32BitMode () ({fixture s 1 17 9 with exception := exception.UNDEFINED [9]}) with | (v,u) => if v then signalException ExceptionType.Illegal_Instr u else u) := by rfl

-- divide_symbolic_REMW_0
example (s : riscv_state) : «dfn'REMW» (0,0,0) ({fixture s 1 17 9 with exception := exception.NoException}) = (match in32BitMode () ({fixture s 1 17 9 with exception := exception.NoException}) with | (v,u) => if v then signalException ExceptionType.Illegal_Instr u else u) := by rfl

-- divide_symbolic_REMW_1
example (s : riscv_state) : «dfn'REMW» (0,0,0) ({fixture s 1 17 9 with exception := exception.UNDEFINED [9]}) = (match in32BitMode () ({fixture s 1 17 9 with exception := exception.UNDEFINED [9]}) with | (v,u) => if v then signalException ExceptionType.Illegal_Instr u else u) := by rfl

-- divide_symbolic_DIVUW_0
example (s : riscv_state) : «dfn'DIVUW» (0,0,0) ({fixture s 1 17 9 with exception := exception.NoException}) = (match in32BitMode () ({fixture s 1 17 9 with exception := exception.NoException}) with | (v,u) => if v then signalException ExceptionType.Illegal_Instr u else u) := by rfl

-- divide_symbolic_DIVUW_1
example (s : riscv_state) : «dfn'DIVUW» (0,0,0) ({fixture s 1 17 9 with exception := exception.UNDEFINED [9]}) = (match in32BitMode () ({fixture s 1 17 9 with exception := exception.UNDEFINED [9]}) with | (v,u) => if v then signalException ExceptionType.Illegal_Instr u else u) := by rfl

-- divide_symbolic_REMUW_0
example (s : riscv_state) : «dfn'REMUW» (0,0,0) ({fixture s 1 17 9 with exception := exception.NoException}) = (match in32BitMode () ({fixture s 1 17 9 with exception := exception.NoException}) with | (v,u) => if v then signalException ExceptionType.Illegal_Instr u else u) := by rfl

-- divide_symbolic_REMUW_1
example (s : riscv_state) : «dfn'REMUW» (0,0,0) ({fixture s 1 17 9 with exception := exception.UNDEFINED [9]}) = (match in32BitMode () ({fixture s 1 17 9 with exception := exception.UNDEFINED [9]}) with | (v,u) => if v then signalException ExceptionType.Illegal_Instr u else u) := by rfl

end Flapjack.Test.L3DivideParity
