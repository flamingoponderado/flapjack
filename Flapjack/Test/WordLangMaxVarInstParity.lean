import Flapjack.Pancake.WordLang.MaxVarInst

namespace Flapjack.Test.WordLangMaxVarInstParity
open Flapjack

-- Kernel replays of freshly captured original HOL rows.
-- mi_skip
example : maxVarInstHOL (width := 64) (.skip) = 0 := by decide

-- mi_const
example : maxVarInstHOL (width := 64) (.const 17 9) = 17 := by decide

-- mi_binop_reg
example : maxVarInstHOL (width := 64) (.arith (.binop .add 3 11 (.reg 17))) = 17 := by decide

-- mi_binop_imm
example : maxVarInstHOL (width := 64) (.arith (.binop .add 3 11 (.imm 99))) = 11 := by decide

-- mi_shift_reg
example : maxVarInstHOL (width := 64) (.arith (.shift .lsl 3 11 (.reg 17))) = 17 := by decide

-- mi_shift_imm
example : maxVarInstHOL (width := 64) (.arith (.shift .lsl 3 11 (.imm 99))) = 11 := by decide

-- mi_div
example : maxVarInstHOL (width := 64) (.arith (.div 3 11 17)) = 17 := by decide

-- mi_addCarry
example : maxVarInstHOL (width := 64) (.arith (.addCarry 3 11 17 5)) = 17 := by decide

-- mi_addOverflow
example : maxVarInstHOL (width := 64) (.arith (.addOverflow 3 11 17 5)) = 17 := by decide

-- mi_subOverflow
example : maxVarInstHOL (width := 64) (.arith (.subOverflow 3 11 17 5)) = 17 := by decide

-- mi_longMul
example : maxVarInstHOL (width := 64) (.arith (.longMul 3 11 17 5)) = 17 := by decide

-- mi_longdiv
example : maxVarInstHOL (width := 64) (.arith (.longDiv 3 11 17 5 23)) = 23 := by decide

-- mi_load
example : maxVarInstHOL (width := 64) (.mem .load 3 (.addr 17 99)) = 17 := by decide

-- mi_store
example : maxVarInstHOL (width := 64) (.mem .store 3 (.addr 17 99)) = 17 := by decide

-- mi_load32
example : maxVarInstHOL (width := 64) (.mem .load32 3 (.addr 17 99)) = 17 := by decide

-- mi_store32
example : maxVarInstHOL (width := 64) (.mem .store32 3 (.addr 17 99)) = 17 := by decide

-- mi_load8
example : maxVarInstHOL (width := 64) (.mem .load8 3 (.addr 17 99)) = 17 := by decide

-- mi_store8
example : maxVarInstHOL (width := 64) (.mem .store8 3 (.addr 17 99)) = 17 := by decide

-- mi_fpLess
example : maxVarInstHOL (width := 64) (.fp (.fpLess 3 99 101)) = 3 := by decide

-- mi_fpLessEqual
example : maxVarInstHOL (width := 64) (.fp (.fpLessEqual 3 99 101)) = 3 := by decide

-- mi_fpEqual
example : maxVarInstHOL (width := 64) (.fp (.fpEqual 3 99 101)) = 3 := by decide

-- mi_toreg64
example : maxVarInstHOL (width := 64) (.fp (.fpMovToReg 3 17 99)) = 3 := by decide

-- mi_fromreg64
example : maxVarInstHOL (width := 64) (.fp (.fpMovFromReg 99 3 17)) = 3 := by decide

-- mi_toreg32
example : maxVarInstHOL (width := 32) (.fp (.fpMovToReg 3 17 99)) = 17 := by decide

-- mi_fromreg32
example : maxVarInstHOL (width := 32) (.fp (.fpMovFromReg 99 3 17)) = 17 := by decide

-- mi_fpdefault
example : maxVarInstHOL (width := 64) (.fp (.fpAdd 99 101 103)) = 0 := by decide

end Flapjack.Test.WordLangMaxVarInstParity
