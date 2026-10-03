import Flapjack.RiscV.L3.Defs.UpperJump

set_option maxRecDepth 20000

namespace Flapjack.Test.L3UpperJumpParity

open Flapjack.RiscV.L3

private def fixture (s : riscv_state) (pc skip src : BitVec 64) : riscv_state :=
 {s with procID := 7, c_PC := fun _ => pc, c_Skip := fun _ => skip, c_gpr := fun id r => if r = 1 then src else s.c_gpr id r}

example (s : riscv_state) : «dfn'LUI» (0,0) (fixture s 1000 4 17) =
 (let t := fixture s 1000 4 17; t) := by
  have numeric : (BitVec.signExtend 64 ((0 : BitVec 20) ++ (0 : BitVec 12))) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'LUI» (0,0) (fixture s 1000 4 17) = (let t := fixture s 1000 4 17; t) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

example (s : riscv_state) : «dfn'LUI» (1,0) (fixture s 1000 4 17) =
 (let t := fixture s 1000 4 17; {t with c_gpr := holUpdate 7 (holUpdate 1 (0) (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : (BitVec.signExtend 64 ((0 : BitVec 20) ++ (0 : BitVec 12))) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'LUI» (1,0) (fixture s 1000 4 17) = (let t := fixture s 1000 4 17; {t with c_gpr := holUpdate 7 (holUpdate 1 (BitVec.signExtend 64 ((0 : BitVec 20) ++ (0 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

example (s : riscv_state) : «dfn'LUI» (7,0) (fixture s 1000 4 17) =
 (let t := fixture s 1000 4 17; {t with c_gpr := holUpdate 7 (holUpdate 7 (0) (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : (BitVec.signExtend 64 ((0 : BitVec 20) ++ (0 : BitVec 12))) = (0 : BitVec 64) := by decide
  have symbolic := (show «dfn'LUI» (7,0) (fixture s 1000 4 17) = (let t := fixture s 1000 4 17; {t with c_gpr := holUpdate 7 (holUpdate 7 (BitVec.signExtend 64 ((0 : BitVec 20) ++ (0 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

example (s : riscv_state) : «dfn'LUI» (0,1) (fixture s 1000 2 17) =
 (let t := fixture s 1000 2 17; t) := by
  have numeric : (BitVec.signExtend 64 ((1 : BitVec 20) ++ (0 : BitVec 12))) = (4096 : BitVec 64) := by decide
  have symbolic := (show «dfn'LUI» (0,1) (fixture s 1000 2 17) = (let t := fixture s 1000 2 17; t) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

example (s : riscv_state) : «dfn'LUI» (1,1) (fixture s 1000 2 17) =
 (let t := fixture s 1000 2 17; {t with c_gpr := holUpdate 7 (holUpdate 1 (4096) (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : (BitVec.signExtend 64 ((1 : BitVec 20) ++ (0 : BitVec 12))) = (4096 : BitVec 64) := by decide
  have symbolic := (show «dfn'LUI» (1,1) (fixture s 1000 2 17) = (let t := fixture s 1000 2 17; {t with c_gpr := holUpdate 7 (holUpdate 1 (BitVec.signExtend 64 ((1 : BitVec 20) ++ (0 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

example (s : riscv_state) : «dfn'LUI» (7,1) (fixture s 1000 2 17) =
 (let t := fixture s 1000 2 17; {t with c_gpr := holUpdate 7 (holUpdate 7 (4096) (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : (BitVec.signExtend 64 ((1 : BitVec 20) ++ (0 : BitVec 12))) = (4096 : BitVec 64) := by decide
  have symbolic := (show «dfn'LUI» (7,1) (fixture s 1000 2 17) = (let t := fixture s 1000 2 17; {t with c_gpr := holUpdate 7 (holUpdate 7 (BitVec.signExtend 64 ((1 : BitVec 20) ++ (0 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

example (s : riscv_state) : «dfn'LUI» (0,524288) (fixture s 1000 4 17) =
 (let t := fixture s 1000 4 17; t) := by
  have numeric : (BitVec.signExtend 64 ((524288 : BitVec 20) ++ (0 : BitVec 12))) = (18446744071562067968 : BitVec 64) := by decide
  have symbolic := (show «dfn'LUI» (0,524288) (fixture s 1000 4 17) = (let t := fixture s 1000 4 17; t) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

example (s : riscv_state) : «dfn'LUI» (1,524288) (fixture s 1000 4 17) =
 (let t := fixture s 1000 4 17; {t with c_gpr := holUpdate 7 (holUpdate 1 (18446744071562067968) (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : (BitVec.signExtend 64 ((524288 : BitVec 20) ++ (0 : BitVec 12))) = (18446744071562067968 : BitVec 64) := by decide
  have symbolic := (show «dfn'LUI» (1,524288) (fixture s 1000 4 17) = (let t := fixture s 1000 4 17; {t with c_gpr := holUpdate 7 (holUpdate 1 (BitVec.signExtend 64 ((524288 : BitVec 20) ++ (0 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

example (s : riscv_state) : «dfn'LUI» (7,524288) (fixture s 1000 4 17) =
 (let t := fixture s 1000 4 17; {t with c_gpr := holUpdate 7 (holUpdate 7 (18446744071562067968) (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : (BitVec.signExtend 64 ((524288 : BitVec 20) ++ (0 : BitVec 12))) = (18446744071562067968 : BitVec 64) := by decide
  have symbolic := (show «dfn'LUI» (7,524288) (fixture s 1000 4 17) = (let t := fixture s 1000 4 17; {t with c_gpr := holUpdate 7 (holUpdate 7 (BitVec.signExtend 64 ((524288 : BitVec 20) ++ (0 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

example (s : riscv_state) : «dfn'LUI» (0,1048575) (fixture s 18446744073709551614 4 18446744073709551615) =
 (let t := fixture s 18446744073709551614 4 18446744073709551615; t) := by
  have numeric : (BitVec.signExtend 64 ((1048575 : BitVec 20) ++ (0 : BitVec 12))) = (18446744073709547520 : BitVec 64) := by decide
  have symbolic := (show «dfn'LUI» (0,1048575) (fixture s 18446744073709551614 4 18446744073709551615) = (let t := fixture s 18446744073709551614 4 18446744073709551615; t) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

example (s : riscv_state) : «dfn'LUI» (1,1048575) (fixture s 18446744073709551614 4 18446744073709551615) =
 (let t := fixture s 18446744073709551614 4 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 (18446744073709547520) (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : (BitVec.signExtend 64 ((1048575 : BitVec 20) ++ (0 : BitVec 12))) = (18446744073709547520 : BitVec 64) := by decide
  have symbolic := (show «dfn'LUI» (1,1048575) (fixture s 18446744073709551614 4 18446744073709551615) = (let t := fixture s 18446744073709551614 4 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 (BitVec.signExtend 64 ((1048575 : BitVec 20) ++ (0 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

example (s : riscv_state) : «dfn'LUI» (7,1048575) (fixture s 18446744073709551614 4 18446744073709551615) =
 (let t := fixture s 18446744073709551614 4 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 (18446744073709547520) (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : (BitVec.signExtend 64 ((1048575 : BitVec 20) ++ (0 : BitVec 12))) = (18446744073709547520 : BitVec 64) := by decide
  have symbolic := (show «dfn'LUI» (7,1048575) (fixture s 18446744073709551614 4 18446744073709551615) = (let t := fixture s 18446744073709551614 4 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 (BitVec.signExtend 64 ((1048575 : BitVec 20) ++ (0 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

example (s : riscv_state) : «dfn'LUI» (0,3) (fixture s 1001 2 18) =
 (let t := fixture s 1001 2 18; t) := by
  have numeric : (BitVec.signExtend 64 ((3 : BitVec 20) ++ (0 : BitVec 12))) = (12288 : BitVec 64) := by decide
  have symbolic := (show «dfn'LUI» (0,3) (fixture s 1001 2 18) = (let t := fixture s 1001 2 18; t) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

example (s : riscv_state) : «dfn'LUI» (1,3) (fixture s 1001 2 18) =
 (let t := fixture s 1001 2 18; {t with c_gpr := holUpdate 7 (holUpdate 1 (12288) (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : (BitVec.signExtend 64 ((3 : BitVec 20) ++ (0 : BitVec 12))) = (12288 : BitVec 64) := by decide
  have symbolic := (show «dfn'LUI» (1,3) (fixture s 1001 2 18) = (let t := fixture s 1001 2 18; {t with c_gpr := holUpdate 7 (holUpdate 1 (BitVec.signExtend 64 ((3 : BitVec 20) ++ (0 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

example (s : riscv_state) : «dfn'LUI» (7,3) (fixture s 1001 2 18) =
 (let t := fixture s 1001 2 18; {t with c_gpr := holUpdate 7 (holUpdate 7 (12288) (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : (BitVec.signExtend 64 ((3 : BitVec 20) ++ (0 : BitVec 12))) = (12288 : BitVec 64) := by decide
  have symbolic := (show «dfn'LUI» (7,3) (fixture s 1001 2 18) = (let t := fixture s 1001 2 18; {t with c_gpr := holUpdate 7 (holUpdate 7 (BitVec.signExtend 64 ((3 : BitVec 20) ++ (0 : BitVec 12))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

example (s : riscv_state) : «dfn'AUIPC» (0,0) (fixture s 1000 4 17) =
 (let t := fixture s 1000 4 17; t) := by
  have numeric : ((1000 : BitVec 64) + (BitVec.signExtend 64 ((0 : BitVec 20) ++ (0 : BitVec 12)))) = (1000 : BitVec 64) := by decide
  have symbolic := (show «dfn'AUIPC» (0,0) (fixture s 1000 4 17) = (let t := fixture s 1000 4 17; t) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

example (s : riscv_state) : «dfn'AUIPC» (1,0) (fixture s 1000 4 17) =
 (let t := fixture s 1000 4 17; {t with c_gpr := holUpdate 7 (holUpdate 1 (1000) (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((1000 : BitVec 64) + (BitVec.signExtend 64 ((0 : BitVec 20) ++ (0 : BitVec 12)))) = (1000 : BitVec 64) := by decide
  have symbolic := (show «dfn'AUIPC» (1,0) (fixture s 1000 4 17) = (let t := fixture s 1000 4 17; {t with c_gpr := holUpdate 7 (holUpdate 1 ((1000 : BitVec 64) + (BitVec.signExtend 64 ((0 : BitVec 20) ++ (0 : BitVec 12)))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

example (s : riscv_state) : «dfn'AUIPC» (7,0) (fixture s 1000 4 17) =
 (let t := fixture s 1000 4 17; {t with c_gpr := holUpdate 7 (holUpdate 7 (1000) (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((1000 : BitVec 64) + (BitVec.signExtend 64 ((0 : BitVec 20) ++ (0 : BitVec 12)))) = (1000 : BitVec 64) := by decide
  have symbolic := (show «dfn'AUIPC» (7,0) (fixture s 1000 4 17) = (let t := fixture s 1000 4 17; {t with c_gpr := holUpdate 7 (holUpdate 7 ((1000 : BitVec 64) + (BitVec.signExtend 64 ((0 : BitVec 20) ++ (0 : BitVec 12)))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

example (s : riscv_state) : «dfn'AUIPC» (0,1) (fixture s 1000 2 17) =
 (let t := fixture s 1000 2 17; t) := by
  have numeric : ((1000 : BitVec 64) + (BitVec.signExtend 64 ((1 : BitVec 20) ++ (0 : BitVec 12)))) = (5096 : BitVec 64) := by decide
  have symbolic := (show «dfn'AUIPC» (0,1) (fixture s 1000 2 17) = (let t := fixture s 1000 2 17; t) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

example (s : riscv_state) : «dfn'AUIPC» (1,1) (fixture s 1000 2 17) =
 (let t := fixture s 1000 2 17; {t with c_gpr := holUpdate 7 (holUpdate 1 (5096) (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((1000 : BitVec 64) + (BitVec.signExtend 64 ((1 : BitVec 20) ++ (0 : BitVec 12)))) = (5096 : BitVec 64) := by decide
  have symbolic := (show «dfn'AUIPC» (1,1) (fixture s 1000 2 17) = (let t := fixture s 1000 2 17; {t with c_gpr := holUpdate 7 (holUpdate 1 ((1000 : BitVec 64) + (BitVec.signExtend 64 ((1 : BitVec 20) ++ (0 : BitVec 12)))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

example (s : riscv_state) : «dfn'AUIPC» (7,1) (fixture s 1000 2 17) =
 (let t := fixture s 1000 2 17; {t with c_gpr := holUpdate 7 (holUpdate 7 (5096) (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((1000 : BitVec 64) + (BitVec.signExtend 64 ((1 : BitVec 20) ++ (0 : BitVec 12)))) = (5096 : BitVec 64) := by decide
  have symbolic := (show «dfn'AUIPC» (7,1) (fixture s 1000 2 17) = (let t := fixture s 1000 2 17; {t with c_gpr := holUpdate 7 (holUpdate 7 ((1000 : BitVec 64) + (BitVec.signExtend 64 ((1 : BitVec 20) ++ (0 : BitVec 12)))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

example (s : riscv_state) : «dfn'AUIPC» (0,524288) (fixture s 1000 4 17) =
 (let t := fixture s 1000 4 17; t) := by
  have numeric : ((1000 : BitVec 64) + (BitVec.signExtend 64 ((524288 : BitVec 20) ++ (0 : BitVec 12)))) = (18446744071562068968 : BitVec 64) := by decide
  have symbolic := (show «dfn'AUIPC» (0,524288) (fixture s 1000 4 17) = (let t := fixture s 1000 4 17; t) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

example (s : riscv_state) : «dfn'AUIPC» (1,524288) (fixture s 1000 4 17) =
 (let t := fixture s 1000 4 17; {t with c_gpr := holUpdate 7 (holUpdate 1 (18446744071562068968) (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((1000 : BitVec 64) + (BitVec.signExtend 64 ((524288 : BitVec 20) ++ (0 : BitVec 12)))) = (18446744071562068968 : BitVec 64) := by decide
  have symbolic := (show «dfn'AUIPC» (1,524288) (fixture s 1000 4 17) = (let t := fixture s 1000 4 17; {t with c_gpr := holUpdate 7 (holUpdate 1 ((1000 : BitVec 64) + (BitVec.signExtend 64 ((524288 : BitVec 20) ++ (0 : BitVec 12)))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

example (s : riscv_state) : «dfn'AUIPC» (7,524288) (fixture s 1000 4 17) =
 (let t := fixture s 1000 4 17; {t with c_gpr := holUpdate 7 (holUpdate 7 (18446744071562068968) (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((1000 : BitVec 64) + (BitVec.signExtend 64 ((524288 : BitVec 20) ++ (0 : BitVec 12)))) = (18446744071562068968 : BitVec 64) := by decide
  have symbolic := (show «dfn'AUIPC» (7,524288) (fixture s 1000 4 17) = (let t := fixture s 1000 4 17; {t with c_gpr := holUpdate 7 (holUpdate 7 ((1000 : BitVec 64) + (BitVec.signExtend 64 ((524288 : BitVec 20) ++ (0 : BitVec 12)))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

example (s : riscv_state) : «dfn'AUIPC» (0,1048575) (fixture s 18446744073709551614 4 18446744073709551615) =
 (let t := fixture s 18446744073709551614 4 18446744073709551615; t) := by
  have numeric : ((18446744073709551614 : BitVec 64) + (BitVec.signExtend 64 ((1048575 : BitVec 20) ++ (0 : BitVec 12)))) = (18446744073709547518 : BitVec 64) := by decide
  have symbolic := (show «dfn'AUIPC» (0,1048575) (fixture s 18446744073709551614 4 18446744073709551615) = (let t := fixture s 18446744073709551614 4 18446744073709551615; t) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

example (s : riscv_state) : «dfn'AUIPC» (1,1048575) (fixture s 18446744073709551614 4 18446744073709551615) =
 (let t := fixture s 18446744073709551614 4 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 (18446744073709547518) (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((18446744073709551614 : BitVec 64) + (BitVec.signExtend 64 ((1048575 : BitVec 20) ++ (0 : BitVec 12)))) = (18446744073709547518 : BitVec 64) := by decide
  have symbolic := (show «dfn'AUIPC» (1,1048575) (fixture s 18446744073709551614 4 18446744073709551615) = (let t := fixture s 18446744073709551614 4 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 1 ((18446744073709551614 : BitVec 64) + (BitVec.signExtend 64 ((1048575 : BitVec 20) ++ (0 : BitVec 12)))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

example (s : riscv_state) : «dfn'AUIPC» (7,1048575) (fixture s 18446744073709551614 4 18446744073709551615) =
 (let t := fixture s 18446744073709551614 4 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 (18446744073709547518) (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((18446744073709551614 : BitVec 64) + (BitVec.signExtend 64 ((1048575 : BitVec 20) ++ (0 : BitVec 12)))) = (18446744073709547518 : BitVec 64) := by decide
  have symbolic := (show «dfn'AUIPC» (7,1048575) (fixture s 18446744073709551614 4 18446744073709551615) = (let t := fixture s 18446744073709551614 4 18446744073709551615; {t with c_gpr := holUpdate 7 (holUpdate 7 ((18446744073709551614 : BitVec 64) + (BitVec.signExtend 64 ((1048575 : BitVec 20) ++ (0 : BitVec 12)))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

example (s : riscv_state) : «dfn'AUIPC» (0,3) (fixture s 1001 2 18) =
 (let t := fixture s 1001 2 18; t) := by
  have numeric : ((1001 : BitVec 64) + (BitVec.signExtend 64 ((3 : BitVec 20) ++ (0 : BitVec 12)))) = (13289 : BitVec 64) := by decide
  have symbolic := (show «dfn'AUIPC» (0,3) (fixture s 1001 2 18) = (let t := fixture s 1001 2 18; t) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

example (s : riscv_state) : «dfn'AUIPC» (1,3) (fixture s 1001 2 18) =
 (let t := fixture s 1001 2 18; {t with c_gpr := holUpdate 7 (holUpdate 1 (13289) (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((1001 : BitVec 64) + (BitVec.signExtend 64 ((3 : BitVec 20) ++ (0 : BitVec 12)))) = (13289 : BitVec 64) := by decide
  have symbolic := (show «dfn'AUIPC» (1,3) (fixture s 1001 2 18) = (let t := fixture s 1001 2 18; {t with c_gpr := holUpdate 7 (holUpdate 1 ((1001 : BitVec 64) + (BitVec.signExtend 64 ((3 : BitVec 20) ++ (0 : BitVec 12)))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

example (s : riscv_state) : «dfn'AUIPC» (7,3) (fixture s 1001 2 18) =
 (let t := fixture s 1001 2 18; {t with c_gpr := holUpdate 7 (holUpdate 7 (13289) (t.c_gpr 7)) t.c_gpr}) := by
  have numeric : ((1001 : BitVec 64) + (BitVec.signExtend 64 ((3 : BitVec 20) ++ (0 : BitVec 12)))) = (13289 : BitVec 64) := by decide
  have symbolic := (show «dfn'AUIPC» (7,3) (fixture s 1001 2 18) = (let t := fixture s 1001 2 18; {t with c_gpr := holUpdate 7 (holUpdate 7 ((1001 : BitVec 64) + (BitVec.signExtend 64 ((3 : BitVec 20) ++ (0 : BitVec 12)))) (t.c_gpr 7)) t.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

example (s : riscv_state) : «dfn'JAL» (0,0) (fixture s 1000 4 17) =
 (let t := fixture s 1000 4 17; (let u := t; {u with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo (1000))) u.c_NextFetch})) := by
  have numeric : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (0 : BitVec 20)) <<< 1)) = (1000 : BitVec 64) := by decide
  change (if ((1000 : BitVec 64) + ((BitVec.signExtend 64 (0 : BitVec 20)) <<< 1)).getLsbD 0 then signalAddressException (ExceptionType.Fetch_Misaligned, ((1000 : BitVec 64) + ((BitVec.signExtend 64 (0 : BitVec 20)) <<< 1))) (fixture s 1000 4 17) else branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (0 : BitVec 20)) <<< 1)) («write'GPR» (((1000 : BitVec 64) + 4), 0) (fixture s 1000 4 17))) = _
  rw [numeric]
  rfl

example (s : riscv_state) : «dfn'JAL» (1,0) (fixture s 1000 4 17) =
 (let t := fixture s 1000 4 17; (let u := {t with c_gpr := holUpdate 7 (holUpdate 1 (1004) (t.c_gpr 7)) t.c_gpr}; {u with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo (1000))) u.c_NextFetch})) := by
  have numeric : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (0 : BitVec 20)) <<< 1)) = (1000 : BitVec 64) := by decide
  change (if ((1000 : BitVec 64) + ((BitVec.signExtend 64 (0 : BitVec 20)) <<< 1)).getLsbD 0 then signalAddressException (ExceptionType.Fetch_Misaligned, ((1000 : BitVec 64) + ((BitVec.signExtend 64 (0 : BitVec 20)) <<< 1))) (fixture s 1000 4 17) else branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (0 : BitVec 20)) <<< 1)) («write'GPR» (((1000 : BitVec 64) + 4), 1) (fixture s 1000 4 17))) = _
  rw [numeric]
  rfl

example (s : riscv_state) : «dfn'JAL» (7,0) (fixture s 1000 4 17) =
 (let t := fixture s 1000 4 17; (let u := {t with c_gpr := holUpdate 7 (holUpdate 7 (1004) (t.c_gpr 7)) t.c_gpr}; {u with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo (1000))) u.c_NextFetch})) := by
  have numeric : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (0 : BitVec 20)) <<< 1)) = (1000 : BitVec 64) := by decide
  change (if ((1000 : BitVec 64) + ((BitVec.signExtend 64 (0 : BitVec 20)) <<< 1)).getLsbD 0 then signalAddressException (ExceptionType.Fetch_Misaligned, ((1000 : BitVec 64) + ((BitVec.signExtend 64 (0 : BitVec 20)) <<< 1))) (fixture s 1000 4 17) else branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (0 : BitVec 20)) <<< 1)) («write'GPR» (((1000 : BitVec 64) + 4), 7) (fixture s 1000 4 17))) = _
  rw [numeric]
  rfl

example (s : riscv_state) : «dfn'JAL» (0,1) (fixture s 1000 2 17) =
 (let t := fixture s 1000 2 17; (let u := t; {u with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo (1002))) u.c_NextFetch})) := by
  have numeric : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 20)) <<< 1)) = (1002 : BitVec 64) := by decide
  change (if ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 20)) <<< 1)).getLsbD 0 then signalAddressException (ExceptionType.Fetch_Misaligned, ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 20)) <<< 1))) (fixture s 1000 2 17) else branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 20)) <<< 1)) («write'GPR» (((1000 : BitVec 64) + 2), 0) (fixture s 1000 2 17))) = _
  rw [numeric]
  rfl

example (s : riscv_state) : «dfn'JAL» (1,1) (fixture s 1000 2 17) =
 (let t := fixture s 1000 2 17; (let u := {t with c_gpr := holUpdate 7 (holUpdate 1 (1002) (t.c_gpr 7)) t.c_gpr}; {u with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo (1002))) u.c_NextFetch})) := by
  have numeric : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 20)) <<< 1)) = (1002 : BitVec 64) := by decide
  change (if ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 20)) <<< 1)).getLsbD 0 then signalAddressException (ExceptionType.Fetch_Misaligned, ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 20)) <<< 1))) (fixture s 1000 2 17) else branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 20)) <<< 1)) («write'GPR» (((1000 : BitVec 64) + 2), 1) (fixture s 1000 2 17))) = _
  rw [numeric]
  rfl

example (s : riscv_state) : «dfn'JAL» (7,1) (fixture s 1000 2 17) =
 (let t := fixture s 1000 2 17; (let u := {t with c_gpr := holUpdate 7 (holUpdate 7 (1002) (t.c_gpr 7)) t.c_gpr}; {u with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo (1002))) u.c_NextFetch})) := by
  have numeric : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 20)) <<< 1)) = (1002 : BitVec 64) := by decide
  change (if ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 20)) <<< 1)).getLsbD 0 then signalAddressException (ExceptionType.Fetch_Misaligned, ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 20)) <<< 1))) (fixture s 1000 2 17) else branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (1 : BitVec 20)) <<< 1)) («write'GPR» (((1000 : BitVec 64) + 2), 7) (fixture s 1000 2 17))) = _
  rw [numeric]
  rfl

example (s : riscv_state) : «dfn'JAL» (0,524288) (fixture s 1000 4 17) =
 (let t := fixture s 1000 4 17; (let u := t; {u with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo (18446744073708504040))) u.c_NextFetch})) := by
  have numeric : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (524288 : BitVec 20)) <<< 1)) = (18446744073708504040 : BitVec 64) := by decide
  change (if ((1000 : BitVec 64) + ((BitVec.signExtend 64 (524288 : BitVec 20)) <<< 1)).getLsbD 0 then signalAddressException (ExceptionType.Fetch_Misaligned, ((1000 : BitVec 64) + ((BitVec.signExtend 64 (524288 : BitVec 20)) <<< 1))) (fixture s 1000 4 17) else branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (524288 : BitVec 20)) <<< 1)) («write'GPR» (((1000 : BitVec 64) + 4), 0) (fixture s 1000 4 17))) = _
  rw [numeric]
  rfl

example (s : riscv_state) : «dfn'JAL» (1,524288) (fixture s 1000 4 17) =
 (let t := fixture s 1000 4 17; (let u := {t with c_gpr := holUpdate 7 (holUpdate 1 (1004) (t.c_gpr 7)) t.c_gpr}; {u with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo (18446744073708504040))) u.c_NextFetch})) := by
  have numeric : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (524288 : BitVec 20)) <<< 1)) = (18446744073708504040 : BitVec 64) := by decide
  change (if ((1000 : BitVec 64) + ((BitVec.signExtend 64 (524288 : BitVec 20)) <<< 1)).getLsbD 0 then signalAddressException (ExceptionType.Fetch_Misaligned, ((1000 : BitVec 64) + ((BitVec.signExtend 64 (524288 : BitVec 20)) <<< 1))) (fixture s 1000 4 17) else branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (524288 : BitVec 20)) <<< 1)) («write'GPR» (((1000 : BitVec 64) + 4), 1) (fixture s 1000 4 17))) = _
  rw [numeric]
  rfl

example (s : riscv_state) : «dfn'JAL» (7,524288) (fixture s 1000 4 17) =
 (let t := fixture s 1000 4 17; (let u := {t with c_gpr := holUpdate 7 (holUpdate 7 (1004) (t.c_gpr 7)) t.c_gpr}; {u with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo (18446744073708504040))) u.c_NextFetch})) := by
  have numeric : ((1000 : BitVec 64) + ((BitVec.signExtend 64 (524288 : BitVec 20)) <<< 1)) = (18446744073708504040 : BitVec 64) := by decide
  change (if ((1000 : BitVec 64) + ((BitVec.signExtend 64 (524288 : BitVec 20)) <<< 1)).getLsbD 0 then signalAddressException (ExceptionType.Fetch_Misaligned, ((1000 : BitVec 64) + ((BitVec.signExtend 64 (524288 : BitVec 20)) <<< 1))) (fixture s 1000 4 17) else branchTo ((1000 : BitVec 64) + ((BitVec.signExtend 64 (524288 : BitVec 20)) <<< 1)) («write'GPR» (((1000 : BitVec 64) + 4), 7) (fixture s 1000 4 17))) = _
  rw [numeric]
  rfl

example (s : riscv_state) : «dfn'JAL» (0,1048575) (fixture s 18446744073709551614 4 18446744073709551615) =
 (let t := fixture s 18446744073709551614 4 18446744073709551615; (let u := t; {u with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo (18446744073709551612))) u.c_NextFetch})) := by
  have numeric : ((18446744073709551614 : BitVec 64) + ((BitVec.signExtend 64 (1048575 : BitVec 20)) <<< 1)) = (18446744073709551612 : BitVec 64) := by decide
  change (if ((18446744073709551614 : BitVec 64) + ((BitVec.signExtend 64 (1048575 : BitVec 20)) <<< 1)).getLsbD 0 then signalAddressException (ExceptionType.Fetch_Misaligned, ((18446744073709551614 : BitVec 64) + ((BitVec.signExtend 64 (1048575 : BitVec 20)) <<< 1))) (fixture s 18446744073709551614 4 18446744073709551615) else branchTo ((18446744073709551614 : BitVec 64) + ((BitVec.signExtend 64 (1048575 : BitVec 20)) <<< 1)) («write'GPR» (((18446744073709551614 : BitVec 64) + 4), 0) (fixture s 18446744073709551614 4 18446744073709551615))) = _
  rw [numeric]
  rfl

example (s : riscv_state) : «dfn'JAL» (1,1048575) (fixture s 18446744073709551614 4 18446744073709551615) =
 (let t := fixture s 18446744073709551614 4 18446744073709551615; (let u := {t with c_gpr := holUpdate 7 (holUpdate 1 (2) (t.c_gpr 7)) t.c_gpr}; {u with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo (18446744073709551612))) u.c_NextFetch})) := by
  have numeric : ((18446744073709551614 : BitVec 64) + ((BitVec.signExtend 64 (1048575 : BitVec 20)) <<< 1)) = (18446744073709551612 : BitVec 64) := by decide
  change (if ((18446744073709551614 : BitVec 64) + ((BitVec.signExtend 64 (1048575 : BitVec 20)) <<< 1)).getLsbD 0 then signalAddressException (ExceptionType.Fetch_Misaligned, ((18446744073709551614 : BitVec 64) + ((BitVec.signExtend 64 (1048575 : BitVec 20)) <<< 1))) (fixture s 18446744073709551614 4 18446744073709551615) else branchTo ((18446744073709551614 : BitVec 64) + ((BitVec.signExtend 64 (1048575 : BitVec 20)) <<< 1)) («write'GPR» (((18446744073709551614 : BitVec 64) + 4), 1) (fixture s 18446744073709551614 4 18446744073709551615))) = _
  rw [numeric]
  rfl

example (s : riscv_state) : «dfn'JAL» (7,1048575) (fixture s 18446744073709551614 4 18446744073709551615) =
 (let t := fixture s 18446744073709551614 4 18446744073709551615; (let u := {t with c_gpr := holUpdate 7 (holUpdate 7 (2) (t.c_gpr 7)) t.c_gpr}; {u with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo (18446744073709551612))) u.c_NextFetch})) := by
  have numeric : ((18446744073709551614 : BitVec 64) + ((BitVec.signExtend 64 (1048575 : BitVec 20)) <<< 1)) = (18446744073709551612 : BitVec 64) := by decide
  change (if ((18446744073709551614 : BitVec 64) + ((BitVec.signExtend 64 (1048575 : BitVec 20)) <<< 1)).getLsbD 0 then signalAddressException (ExceptionType.Fetch_Misaligned, ((18446744073709551614 : BitVec 64) + ((BitVec.signExtend 64 (1048575 : BitVec 20)) <<< 1))) (fixture s 18446744073709551614 4 18446744073709551615) else branchTo ((18446744073709551614 : BitVec 64) + ((BitVec.signExtend 64 (1048575 : BitVec 20)) <<< 1)) («write'GPR» (((18446744073709551614 : BitVec 64) + 4), 7) (fixture s 18446744073709551614 4 18446744073709551615))) = _
  rw [numeric]
  rfl

example (s : riscv_state) : «dfn'JAL» (0,3) (fixture s 1001 2 18) =
 (let t := fixture s 1001 2 18; setTrap (ExceptionType.Fetch_Misaligned, some (1007)) t) := by
  have numeric : ((1001 : BitVec 64) + ((BitVec.signExtend 64 (3 : BitVec 20)) <<< 1)) = (1007 : BitVec 64) := by decide
  change (if ((1001 : BitVec 64) + ((BitVec.signExtend 64 (3 : BitVec 20)) <<< 1)).getLsbD 0 then signalAddressException (ExceptionType.Fetch_Misaligned, ((1001 : BitVec 64) + ((BitVec.signExtend 64 (3 : BitVec 20)) <<< 1))) (fixture s 1001 2 18) else branchTo ((1001 : BitVec 64) + ((BitVec.signExtend 64 (3 : BitVec 20)) <<< 1)) («write'GPR» (((1001 : BitVec 64) + 2), 0) (fixture s 1001 2 18))) = _
  rw [numeric]
  rfl

example (s : riscv_state) : «dfn'JAL» (1,3) (fixture s 1001 2 18) =
 (let t := fixture s 1001 2 18; setTrap (ExceptionType.Fetch_Misaligned, some (1007)) t) := by
  have numeric : ((1001 : BitVec 64) + ((BitVec.signExtend 64 (3 : BitVec 20)) <<< 1)) = (1007 : BitVec 64) := by decide
  change (if ((1001 : BitVec 64) + ((BitVec.signExtend 64 (3 : BitVec 20)) <<< 1)).getLsbD 0 then signalAddressException (ExceptionType.Fetch_Misaligned, ((1001 : BitVec 64) + ((BitVec.signExtend 64 (3 : BitVec 20)) <<< 1))) (fixture s 1001 2 18) else branchTo ((1001 : BitVec 64) + ((BitVec.signExtend 64 (3 : BitVec 20)) <<< 1)) («write'GPR» (((1001 : BitVec 64) + 2), 1) (fixture s 1001 2 18))) = _
  rw [numeric]
  rfl

example (s : riscv_state) : «dfn'JAL» (7,3) (fixture s 1001 2 18) =
 (let t := fixture s 1001 2 18; setTrap (ExceptionType.Fetch_Misaligned, some (1007)) t) := by
  have numeric : ((1001 : BitVec 64) + ((BitVec.signExtend 64 (3 : BitVec 20)) <<< 1)) = (1007 : BitVec 64) := by decide
  change (if ((1001 : BitVec 64) + ((BitVec.signExtend 64 (3 : BitVec 20)) <<< 1)).getLsbD 0 then signalAddressException (ExceptionType.Fetch_Misaligned, ((1001 : BitVec 64) + ((BitVec.signExtend 64 (3 : BitVec 20)) <<< 1))) (fixture s 1001 2 18) else branchTo ((1001 : BitVec 64) + ((BitVec.signExtend 64 (3 : BitVec 20)) <<< 1)) («write'GPR» (((1001 : BitVec 64) + 2), 7) (fixture s 1001 2 18))) = _
  rw [numeric]
  rfl

example (s : riscv_state) : «dfn'JALR» (0,1,0) (fixture s 1000 4 17) =
 (let t := fixture s 1000 4 17; (let u := t; {u with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo (16))) u.c_NextFetch})) := by
  have numeric : (((17 : BitVec 64) + (BitVec.signExtend 64 (0 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))) = (16 : BitVec 64) := by decide
  change (if (((17 : BitVec 64) + (BitVec.signExtend 64 (0 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))).getLsbD 0 then signalAddressException (ExceptionType.Fetch_Misaligned, (((17 : BitVec 64) + (BitVec.signExtend 64 (0 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2)))) (fixture s 1000 4 17) else branchTo (((17 : BitVec 64) + (BitVec.signExtend 64 (0 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))) («write'GPR» (((1000 : BitVec 64) + 4), 0) (fixture s 1000 4 17))) = _
  rw [numeric]
  rfl

example (s : riscv_state) : «dfn'JALR» (1,1,0) (fixture s 1000 4 17) =
 (let t := fixture s 1000 4 17; (let u := {t with c_gpr := holUpdate 7 (holUpdate 1 (1004) (t.c_gpr 7)) t.c_gpr}; {u with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo (16))) u.c_NextFetch})) := by
  have numeric : (((17 : BitVec 64) + (BitVec.signExtend 64 (0 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))) = (16 : BitVec 64) := by decide
  change (if (((17 : BitVec 64) + (BitVec.signExtend 64 (0 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))).getLsbD 0 then signalAddressException (ExceptionType.Fetch_Misaligned, (((17 : BitVec 64) + (BitVec.signExtend 64 (0 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2)))) (fixture s 1000 4 17) else branchTo (((17 : BitVec 64) + (BitVec.signExtend 64 (0 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))) («write'GPR» (((1000 : BitVec 64) + 4), 1) (fixture s 1000 4 17))) = _
  rw [numeric]
  rfl

example (s : riscv_state) : «dfn'JALR» (7,1,0) (fixture s 1000 4 17) =
 (let t := fixture s 1000 4 17; (let u := {t with c_gpr := holUpdate 7 (holUpdate 7 (1004) (t.c_gpr 7)) t.c_gpr}; {u with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo (16))) u.c_NextFetch})) := by
  have numeric : (((17 : BitVec 64) + (BitVec.signExtend 64 (0 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))) = (16 : BitVec 64) := by decide
  change (if (((17 : BitVec 64) + (BitVec.signExtend 64 (0 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))).getLsbD 0 then signalAddressException (ExceptionType.Fetch_Misaligned, (((17 : BitVec 64) + (BitVec.signExtend 64 (0 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2)))) (fixture s 1000 4 17) else branchTo (((17 : BitVec 64) + (BitVec.signExtend 64 (0 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))) («write'GPR» (((1000 : BitVec 64) + 4), 7) (fixture s 1000 4 17))) = _
  rw [numeric]
  rfl

example (s : riscv_state) : «dfn'JALR» (0,1,1) (fixture s 1000 2 17) =
 (let t := fixture s 1000 2 17; (let u := t; {u with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo (18))) u.c_NextFetch})) := by
  have numeric : (((17 : BitVec 64) + (BitVec.signExtend 64 (1 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))) = (18 : BitVec 64) := by decide
  change (if (((17 : BitVec 64) + (BitVec.signExtend 64 (1 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))).getLsbD 0 then signalAddressException (ExceptionType.Fetch_Misaligned, (((17 : BitVec 64) + (BitVec.signExtend 64 (1 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2)))) (fixture s 1000 2 17) else branchTo (((17 : BitVec 64) + (BitVec.signExtend 64 (1 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))) («write'GPR» (((1000 : BitVec 64) + 2), 0) (fixture s 1000 2 17))) = _
  rw [numeric]
  rfl

example (s : riscv_state) : «dfn'JALR» (1,1,1) (fixture s 1000 2 17) =
 (let t := fixture s 1000 2 17; (let u := {t with c_gpr := holUpdate 7 (holUpdate 1 (1002) (t.c_gpr 7)) t.c_gpr}; {u with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo (18))) u.c_NextFetch})) := by
  have numeric : (((17 : BitVec 64) + (BitVec.signExtend 64 (1 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))) = (18 : BitVec 64) := by decide
  change (if (((17 : BitVec 64) + (BitVec.signExtend 64 (1 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))).getLsbD 0 then signalAddressException (ExceptionType.Fetch_Misaligned, (((17 : BitVec 64) + (BitVec.signExtend 64 (1 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2)))) (fixture s 1000 2 17) else branchTo (((17 : BitVec 64) + (BitVec.signExtend 64 (1 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))) («write'GPR» (((1000 : BitVec 64) + 2), 1) (fixture s 1000 2 17))) = _
  rw [numeric]
  rfl

example (s : riscv_state) : «dfn'JALR» (7,1,1) (fixture s 1000 2 17) =
 (let t := fixture s 1000 2 17; (let u := {t with c_gpr := holUpdate 7 (holUpdate 7 (1002) (t.c_gpr 7)) t.c_gpr}; {u with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo (18))) u.c_NextFetch})) := by
  have numeric : (((17 : BitVec 64) + (BitVec.signExtend 64 (1 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))) = (18 : BitVec 64) := by decide
  change (if (((17 : BitVec 64) + (BitVec.signExtend 64 (1 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))).getLsbD 0 then signalAddressException (ExceptionType.Fetch_Misaligned, (((17 : BitVec 64) + (BitVec.signExtend 64 (1 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2)))) (fixture s 1000 2 17) else branchTo (((17 : BitVec 64) + (BitVec.signExtend 64 (1 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))) («write'GPR» (((1000 : BitVec 64) + 2), 7) (fixture s 1000 2 17))) = _
  rw [numeric]
  rfl

example (s : riscv_state) : «dfn'JALR» (0,1,2048) (fixture s 1000 4 17) =
 (let t := fixture s 1000 4 17; (let u := t; {u with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo (18446744073709549584))) u.c_NextFetch})) := by
  have numeric : (((17 : BitVec 64) + (BitVec.signExtend 64 (2048 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))) = (18446744073709549584 : BitVec 64) := by decide
  change (if (((17 : BitVec 64) + (BitVec.signExtend 64 (2048 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))).getLsbD 0 then signalAddressException (ExceptionType.Fetch_Misaligned, (((17 : BitVec 64) + (BitVec.signExtend 64 (2048 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2)))) (fixture s 1000 4 17) else branchTo (((17 : BitVec 64) + (BitVec.signExtend 64 (2048 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))) («write'GPR» (((1000 : BitVec 64) + 4), 0) (fixture s 1000 4 17))) = _
  rw [numeric]
  rfl

example (s : riscv_state) : «dfn'JALR» (1,1,2048) (fixture s 1000 4 17) =
 (let t := fixture s 1000 4 17; (let u := {t with c_gpr := holUpdate 7 (holUpdate 1 (1004) (t.c_gpr 7)) t.c_gpr}; {u with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo (18446744073709549584))) u.c_NextFetch})) := by
  have numeric : (((17 : BitVec 64) + (BitVec.signExtend 64 (2048 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))) = (18446744073709549584 : BitVec 64) := by decide
  change (if (((17 : BitVec 64) + (BitVec.signExtend 64 (2048 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))).getLsbD 0 then signalAddressException (ExceptionType.Fetch_Misaligned, (((17 : BitVec 64) + (BitVec.signExtend 64 (2048 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2)))) (fixture s 1000 4 17) else branchTo (((17 : BitVec 64) + (BitVec.signExtend 64 (2048 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))) («write'GPR» (((1000 : BitVec 64) + 4), 1) (fixture s 1000 4 17))) = _
  rw [numeric]
  rfl

example (s : riscv_state) : «dfn'JALR» (7,1,2048) (fixture s 1000 4 17) =
 (let t := fixture s 1000 4 17; (let u := {t with c_gpr := holUpdate 7 (holUpdate 7 (1004) (t.c_gpr 7)) t.c_gpr}; {u with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo (18446744073709549584))) u.c_NextFetch})) := by
  have numeric : (((17 : BitVec 64) + (BitVec.signExtend 64 (2048 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))) = (18446744073709549584 : BitVec 64) := by decide
  change (if (((17 : BitVec 64) + (BitVec.signExtend 64 (2048 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))).getLsbD 0 then signalAddressException (ExceptionType.Fetch_Misaligned, (((17 : BitVec 64) + (BitVec.signExtend 64 (2048 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2)))) (fixture s 1000 4 17) else branchTo (((17 : BitVec 64) + (BitVec.signExtend 64 (2048 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))) («write'GPR» (((1000 : BitVec 64) + 4), 7) (fixture s 1000 4 17))) = _
  rw [numeric]
  rfl

example (s : riscv_state) : «dfn'JALR» (0,1,4095) (fixture s 18446744073709551614 4 18446744073709551615) =
 (let t := fixture s 18446744073709551614 4 18446744073709551615; (let u := t; {u with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo (18446744073709551614))) u.c_NextFetch})) := by
  have numeric : (((18446744073709551615 : BitVec 64) + (BitVec.signExtend 64 (4095 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))) = (18446744073709551614 : BitVec 64) := by decide
  change (if (((18446744073709551615 : BitVec 64) + (BitVec.signExtend 64 (4095 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))).getLsbD 0 then signalAddressException (ExceptionType.Fetch_Misaligned, (((18446744073709551615 : BitVec 64) + (BitVec.signExtend 64 (4095 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2)))) (fixture s 18446744073709551614 4 18446744073709551615) else branchTo (((18446744073709551615 : BitVec 64) + (BitVec.signExtend 64 (4095 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))) («write'GPR» (((18446744073709551614 : BitVec 64) + 4), 0) (fixture s 18446744073709551614 4 18446744073709551615))) = _
  rw [numeric]
  rfl

example (s : riscv_state) : «dfn'JALR» (1,1,4095) (fixture s 18446744073709551614 4 18446744073709551615) =
 (let t := fixture s 18446744073709551614 4 18446744073709551615; (let u := {t with c_gpr := holUpdate 7 (holUpdate 1 (2) (t.c_gpr 7)) t.c_gpr}; {u with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo (18446744073709551614))) u.c_NextFetch})) := by
  have numeric : (((18446744073709551615 : BitVec 64) + (BitVec.signExtend 64 (4095 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))) = (18446744073709551614 : BitVec 64) := by decide
  change (if (((18446744073709551615 : BitVec 64) + (BitVec.signExtend 64 (4095 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))).getLsbD 0 then signalAddressException (ExceptionType.Fetch_Misaligned, (((18446744073709551615 : BitVec 64) + (BitVec.signExtend 64 (4095 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2)))) (fixture s 18446744073709551614 4 18446744073709551615) else branchTo (((18446744073709551615 : BitVec 64) + (BitVec.signExtend 64 (4095 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))) («write'GPR» (((18446744073709551614 : BitVec 64) + 4), 1) (fixture s 18446744073709551614 4 18446744073709551615))) = _
  rw [numeric]
  rfl

example (s : riscv_state) : «dfn'JALR» (7,1,4095) (fixture s 18446744073709551614 4 18446744073709551615) =
 (let t := fixture s 18446744073709551614 4 18446744073709551615; (let u := {t with c_gpr := holUpdate 7 (holUpdate 7 (2) (t.c_gpr 7)) t.c_gpr}; {u with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo (18446744073709551614))) u.c_NextFetch})) := by
  have numeric : (((18446744073709551615 : BitVec 64) + (BitVec.signExtend 64 (4095 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))) = (18446744073709551614 : BitVec 64) := by decide
  change (if (((18446744073709551615 : BitVec 64) + (BitVec.signExtend 64 (4095 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))).getLsbD 0 then signalAddressException (ExceptionType.Fetch_Misaligned, (((18446744073709551615 : BitVec 64) + (BitVec.signExtend 64 (4095 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2)))) (fixture s 18446744073709551614 4 18446744073709551615) else branchTo (((18446744073709551615 : BitVec 64) + (BitVec.signExtend 64 (4095 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))) («write'GPR» (((18446744073709551614 : BitVec 64) + 4), 7) (fixture s 18446744073709551614 4 18446744073709551615))) = _
  rw [numeric]
  rfl

example (s : riscv_state) : «dfn'JALR» (0,1,3) (fixture s 1001 2 18) =
 (let t := fixture s 1001 2 18; (let u := t; {u with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo (20))) u.c_NextFetch})) := by
  have numeric : (((18 : BitVec 64) + (BitVec.signExtend 64 (3 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))) = (20 : BitVec 64) := by decide
  change (if (((18 : BitVec 64) + (BitVec.signExtend 64 (3 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))).getLsbD 0 then signalAddressException (ExceptionType.Fetch_Misaligned, (((18 : BitVec 64) + (BitVec.signExtend 64 (3 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2)))) (fixture s 1001 2 18) else branchTo (((18 : BitVec 64) + (BitVec.signExtend 64 (3 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))) («write'GPR» (((1001 : BitVec 64) + 2), 0) (fixture s 1001 2 18))) = _
  rw [numeric]
  rfl

example (s : riscv_state) : «dfn'JALR» (1,1,3) (fixture s 1001 2 18) =
 (let t := fixture s 1001 2 18; (let u := {t with c_gpr := holUpdate 7 (holUpdate 1 (1003) (t.c_gpr 7)) t.c_gpr}; {u with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo (20))) u.c_NextFetch})) := by
  have numeric : (((18 : BitVec 64) + (BitVec.signExtend 64 (3 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))) = (20 : BitVec 64) := by decide
  change (if (((18 : BitVec 64) + (BitVec.signExtend 64 (3 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))).getLsbD 0 then signalAddressException (ExceptionType.Fetch_Misaligned, (((18 : BitVec 64) + (BitVec.signExtend 64 (3 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2)))) (fixture s 1001 2 18) else branchTo (((18 : BitVec 64) + (BitVec.signExtend 64 (3 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))) («write'GPR» (((1001 : BitVec 64) + 2), 1) (fixture s 1001 2 18))) = _
  rw [numeric]
  rfl

example (s : riscv_state) : «dfn'JALR» (7,1,3) (fixture s 1001 2 18) =
 (let t := fixture s 1001 2 18; (let u := {t with c_gpr := holUpdate 7 (holUpdate 7 (1003) (t.c_gpr 7)) t.c_gpr}; {u with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo (20))) u.c_NextFetch})) := by
  have numeric : (((18 : BitVec 64) + (BitVec.signExtend 64 (3 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))) = (20 : BitVec 64) := by decide
  change (if (((18 : BitVec 64) + (BitVec.signExtend 64 (3 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))).getLsbD 0 then signalAddressException (ExceptionType.Fetch_Misaligned, (((18 : BitVec 64) + (BitVec.signExtend 64 (3 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2)))) (fixture s 1001 2 18) else branchTo (((18 : BitVec 64) + (BitVec.signExtend 64 (3 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))) («write'GPR» (((1001 : BitVec 64) + 2), 7) (fixture s 1001 2 18))) = _
  rw [numeric]
  rfl

example (s : riscv_state) : «dfn'JALR» (0,0,0) (fixture s 1000 4 17) =
 (let t := (fixture s 1000 4 17); let u := t; {u with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 0)) u.c_NextFetch}) := by
  have numeric : (((0 : BitVec 64) + (BitVec.signExtend 64 (0 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))) = (0 : BitVec 64) := by decide
  change (if (((0 : BitVec 64) + (BitVec.signExtend 64 (0 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))).getLsbD 0 then signalAddressException (ExceptionType.Fetch_Misaligned, (((0 : BitVec 64) + (BitVec.signExtend 64 (0 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2)))) (fixture s 1000 4 17) else branchTo (((0 : BitVec 64) + (BitVec.signExtend 64 (0 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))) («write'GPR» (1004,0) (fixture s 1000 4 17))) = _
  rw [numeric]
  rfl

example (s : riscv_state) : «dfn'JALR» (1,0,0) (fixture s 1000 4 17) =
 (let t := (fixture s 1000 4 17); let u := {t with c_gpr := holUpdate 7 (holUpdate 1 1004 (t.c_gpr 7)) t.c_gpr}; {u with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 0)) u.c_NextFetch}) := by
  have numeric : (((0 : BitVec 64) + (BitVec.signExtend 64 (0 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))) = (0 : BitVec 64) := by decide
  change (if (((0 : BitVec 64) + (BitVec.signExtend 64 (0 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))).getLsbD 0 then signalAddressException (ExceptionType.Fetch_Misaligned, (((0 : BitVec 64) + (BitVec.signExtend 64 (0 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2)))) (fixture s 1000 4 17) else branchTo (((0 : BitVec 64) + (BitVec.signExtend 64 (0 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))) («write'GPR» (1004,1) (fixture s 1000 4 17))) = _
  rw [numeric]
  rfl

example (s : riscv_state) : «dfn'JALR» (7,0,0) (fixture s 1000 4 17) =
 (let t := (fixture s 1000 4 17); let u := {t with c_gpr := holUpdate 7 (holUpdate 7 1004 (t.c_gpr 7)) t.c_gpr}; {u with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 0)) u.c_NextFetch}) := by
  have numeric : (((0 : BitVec 64) + (BitVec.signExtend 64 (0 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))) = (0 : BitVec 64) := by decide
  change (if (((0 : BitVec 64) + (BitVec.signExtend 64 (0 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))).getLsbD 0 then signalAddressException (ExceptionType.Fetch_Misaligned, (((0 : BitVec 64) + (BitVec.signExtend 64 (0 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2)))) (fixture s 1000 4 17) else branchTo (((0 : BitVec 64) + (BitVec.signExtend 64 (0 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))) («write'GPR» (1004,7) (fixture s 1000 4 17))) = _
  rw [numeric]
  rfl

example (s : riscv_state) : «dfn'JALR» (0,0,1) (fixture s 1000 4 17) =
 (let t := (fixture s 1000 4 17); let u := t; {u with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 0)) u.c_NextFetch}) := by
  have numeric : (((0 : BitVec 64) + (BitVec.signExtend 64 (1 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))) = (0 : BitVec 64) := by decide
  change (if (((0 : BitVec 64) + (BitVec.signExtend 64 (1 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))).getLsbD 0 then signalAddressException (ExceptionType.Fetch_Misaligned, (((0 : BitVec 64) + (BitVec.signExtend 64 (1 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2)))) (fixture s 1000 4 17) else branchTo (((0 : BitVec 64) + (BitVec.signExtend 64 (1 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))) («write'GPR» (1004,0) (fixture s 1000 4 17))) = _
  rw [numeric]
  rfl

example (s : riscv_state) : «dfn'JALR» (1,0,1) (fixture s 1000 4 17) =
 (let t := (fixture s 1000 4 17); let u := {t with c_gpr := holUpdate 7 (holUpdate 1 1004 (t.c_gpr 7)) t.c_gpr}; {u with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 0)) u.c_NextFetch}) := by
  have numeric : (((0 : BitVec 64) + (BitVec.signExtend 64 (1 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))) = (0 : BitVec 64) := by decide
  change (if (((0 : BitVec 64) + (BitVec.signExtend 64 (1 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))).getLsbD 0 then signalAddressException (ExceptionType.Fetch_Misaligned, (((0 : BitVec 64) + (BitVec.signExtend 64 (1 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2)))) (fixture s 1000 4 17) else branchTo (((0 : BitVec 64) + (BitVec.signExtend 64 (1 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))) («write'GPR» (1004,1) (fixture s 1000 4 17))) = _
  rw [numeric]
  rfl

example (s : riscv_state) : «dfn'JALR» (7,0,1) (fixture s 1000 4 17) =
 (let t := (fixture s 1000 4 17); let u := {t with c_gpr := holUpdate 7 (holUpdate 7 1004 (t.c_gpr 7)) t.c_gpr}; {u with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 0)) u.c_NextFetch}) := by
  have numeric : (((0 : BitVec 64) + (BitVec.signExtend 64 (1 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))) = (0 : BitVec 64) := by decide
  change (if (((0 : BitVec 64) + (BitVec.signExtend 64 (1 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))).getLsbD 0 then signalAddressException (ExceptionType.Fetch_Misaligned, (((0 : BitVec 64) + (BitVec.signExtend 64 (1 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2)))) (fixture s 1000 4 17) else branchTo (((0 : BitVec 64) + (BitVec.signExtend 64 (1 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))) («write'GPR» (1004,7) (fixture s 1000 4 17))) = _
  rw [numeric]
  rfl

example (s : riscv_state) : «dfn'JALR» (0,0,4095) (fixture s 1000 4 17) =
 (let t := (fixture s 1000 4 17); let u := t; {u with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 18446744073709551614)) u.c_NextFetch}) := by
  have numeric : (((0 : BitVec 64) + (BitVec.signExtend 64 (4095 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))) = (18446744073709551614 : BitVec 64) := by decide
  change (if (((0 : BitVec 64) + (BitVec.signExtend 64 (4095 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))).getLsbD 0 then signalAddressException (ExceptionType.Fetch_Misaligned, (((0 : BitVec 64) + (BitVec.signExtend 64 (4095 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2)))) (fixture s 1000 4 17) else branchTo (((0 : BitVec 64) + (BitVec.signExtend 64 (4095 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))) («write'GPR» (1004,0) (fixture s 1000 4 17))) = _
  rw [numeric]
  rfl

example (s : riscv_state) : «dfn'JALR» (1,0,4095) (fixture s 1000 4 17) =
 (let t := (fixture s 1000 4 17); let u := {t with c_gpr := holUpdate 7 (holUpdate 1 1004 (t.c_gpr 7)) t.c_gpr}; {u with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 18446744073709551614)) u.c_NextFetch}) := by
  have numeric : (((0 : BitVec 64) + (BitVec.signExtend 64 (4095 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))) = (18446744073709551614 : BitVec 64) := by decide
  change (if (((0 : BitVec 64) + (BitVec.signExtend 64 (4095 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))).getLsbD 0 then signalAddressException (ExceptionType.Fetch_Misaligned, (((0 : BitVec 64) + (BitVec.signExtend 64 (4095 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2)))) (fixture s 1000 4 17) else branchTo (((0 : BitVec 64) + (BitVec.signExtend 64 (4095 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))) («write'GPR» (1004,1) (fixture s 1000 4 17))) = _
  rw [numeric]
  rfl

example (s : riscv_state) : «dfn'JALR» (7,0,4095) (fixture s 1000 4 17) =
 (let t := (fixture s 1000 4 17); let u := {t with c_gpr := holUpdate 7 (holUpdate 7 1004 (t.c_gpr 7)) t.c_gpr}; {u with c_NextFetch := holUpdate 7 (some (TransferControl.BranchTo 18446744073709551614)) u.c_NextFetch}) := by
  have numeric : (((0 : BitVec 64) + (BitVec.signExtend 64 (4095 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))) = (18446744073709551614 : BitVec 64) := by decide
  change (if (((0 : BitVec 64) + (BitVec.signExtend 64 (4095 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))).getLsbD 0 then signalAddressException (ExceptionType.Fetch_Misaligned, (((0 : BitVec 64) + (BitVec.signExtend 64 (4095 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2)))) (fixture s 1000 4 17) else branchTo (((0 : BitVec 64) + (BitVec.signExtend 64 (4095 : BitVec 12))) &&& (BitVec.signExtend 64 (2 : BitVec 2))) («write'GPR» (1004,7) (fixture s 1000 4 17))) = _
  rw [numeric]
  rfl

example (s : riscv_state) : Skip s = s.c_Skip s.procID := by rfl

example (s : riscv_state) (pc : BitVec 64) : branchTo pc s = {s with c_NextFetch := holUpdate s.procID (some (TransferControl.BranchTo pc)) s.c_NextFetch} := by rfl

end Flapjack.Test.L3UpperJumpParity
