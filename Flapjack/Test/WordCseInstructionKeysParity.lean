import Flapjack.Compiler.Backend.WordCse.InstructionKeys
namespace Flapjack.Test.WordCseInstructionKeysParity
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.WordCse
-- key_shift_lsl
example : shiftToNum .lsl = 40 := by rfl

-- key_shift_lsr
example : shiftToNum .lsr = 41 := by rfl

-- key_shift_asr
example : shiftToNum .asr = 42 := by rfl

-- key_shift_ror
example : shiftToNum .ror = 43 := by rfl

-- key_op_add
example : arithOpToNum .add = 35 := by rfl

-- key_heap_add
example : opCurrHeapToNumList .add 7 = [0, 35, 107] := by rfl

-- key_op_sub
example : arithOpToNum .sub = 36 := by rfl

-- key_heap_sub
example : opCurrHeapToNumList .sub 7 = [0, 36, 107] := by rfl

-- key_op_and
example : arithOpToNum .and = 37 := by rfl

-- key_heap_and
example : opCurrHeapToNumList .and 7 = [0, 37, 107] := by rfl

-- key_op_or
example : arithOpToNum .or = 38 := by rfl

-- key_heap_or
example : opCurrHeapToNumList .or 7 = [0, 38, 107] := by rfl

-- key_op_xor
example : arithOpToNum .xor = 39 := by rfl

-- key_heap_xor
example : opCurrHeapToNumList .xor 7 = [0, 39, 107] := by rfl

-- key_mem_load
example : memOpToNum .load = 21 := by rfl

-- key_load_load
example : loadToNumList .load 9 (255 : BitVec 8) = [21, 109, 255] := by rfl

-- key_mem_load8
example : memOpToNum .load8 = 22 := by rfl

-- key_load_load8
example : loadToNumList .load8 9 (255 : BitVec 8) = [22, 109, 255] := by rfl

-- key_mem_load16
example : memOpToNum .load16 = 46 := by rfl

-- key_load_load16
example : loadToNumList .load16 9 (255 : BitVec 8) = [46, 109, 255] := by rfl

-- key_mem_load32
example : memOpToNum .load32 = 44 := by rfl

-- key_load_load32
example : loadToNumList .load32 9 (255 : BitVec 8) = [44, 109, 255] := by rfl

-- key_mem_store
example : memOpToNum .store = 23 := by rfl

-- key_load_store
example : loadToNumList .store 9 (255 : BitVec 8) = [23, 109, 255] := by rfl

-- key_mem_store8
example : memOpToNum .store8 = 47 := by rfl

-- key_load_store8
example : loadToNumList .store8 9 (255 : BitVec 8) = [47, 109, 255] := by rfl

-- key_mem_store16
example : memOpToNum .store16 = 24 := by rfl

-- key_load_store16
example : loadToNumList .store16 9 (255 : BitVec 8) = [24, 109, 255] := by rfl

-- key_mem_store32
example : memOpToNum .store32 = 45 := by rfl

-- key_load_store32
example : loadToNumList .store32 9 (255 : BitVec 8) = [45, 109, 255] := by rfl

-- key_word_1
example : wordToNum (-1 : BitVec 1) = 1 := by rfl

-- key_imm_1
example : regImmToNumList (.imm (-1 : BitVec 1)) = [34, 1] := by rfl

-- key_const_1
example : instToNumList (.const 99 (-1 : BitVec 1)) = [2, 1] := by rfl

-- key_word_32
example : wordToNum (-1 : BitVec 32) = 4294967295 := by rfl

-- key_imm_32
example : regImmToNumList (.imm (-1 : BitVec 32)) = [34, 4294967295] := by rfl

-- key_const_32
example : instToNumList (.const 99 (-1 : BitVec 32)) = [2, 4294967295] := by rfl

-- key_word_64
example : wordToNum (-1 : BitVec 64) = 18446744073709551615 := by rfl

-- key_imm_64
example : regImmToNumList (.imm (-1 : BitVec 64)) = [34, 18446744073709551615] := by rfl

-- key_const_64
example : instToNumList (.const 99 (-1 : BitVec 64)) = [2, 18446744073709551615] := by rfl

-- key_word_80
example : wordToNum (-1 : BitVec 80) = 1208925819614629174706175 := by rfl

-- key_imm_80
example : regImmToNumList (.imm (-1 : BitVec 80)) = [34, 1208925819614629174706175] := by rfl

-- key_const_80
example : instToNumList (.const 99 (-1 : BitVec 80)) = [2, 1208925819614629174706175] := by rfl

-- key_reg
example : regImmToNumList (width := 8) (.reg 777) = [33, 877] := by rfl

-- key_arith_0
example : arithToNumList (width := 8) (.binop .add 99 2 (.reg 3)) = [25, 35, 102, 33, 103] := by rfl

-- key_inst_arith_0
example : instToNumList (width := 8) (.arith (.binop .add 99 2 (.reg 3))) = [3, 25, 35, 102, 33, 103] := by rfl

-- key_arith_1
example : arithToNumList (width := 8) (.longMul 99 98 2 3) = [26, 102, 103] := by rfl

-- key_inst_arith_1
example : instToNumList (width := 8) (.arith (.longMul 99 98 2 3)) = [3, 26, 102, 103] := by rfl

-- key_arith_2
example : arithToNumList (width := 8) (.longDiv 99 98 2 3 4) = [27, 102, 103, 104] := by rfl

-- key_inst_arith_2
example : instToNumList (width := 8) (.arith (.longDiv 99 98 2 3 4)) = [3, 27, 102, 103, 104] := by rfl

-- key_arith_3
example : arithToNumList (width := 8) (.shift .ror 99 2 (.imm 255)) = [28, 43, 102, 34, 255] := by rfl

-- key_inst_arith_3
example : instToNumList (width := 8) (.arith (.shift .ror 99 2 (.imm 255))) = [3, 28, 43, 102, 34, 255] := by rfl

-- key_arith_4
example : arithToNumList (width := 8) (.div 99 2 3) = [29, 102, 103] := by rfl

-- key_inst_arith_4
example : instToNumList (width := 8) (.arith (.div 99 2 3)) = [3, 29, 102, 103] := by rfl

-- key_arith_5
example : arithToNumList (width := 8) (.addCarry 99 2 3 98) = [30, 102, 103] := by rfl

-- key_inst_arith_5
example : instToNumList (width := 8) (.arith (.addCarry 99 2 3 98)) = [3, 30, 102, 103] := by rfl

-- key_arith_6
example : arithToNumList (width := 8) (.addOverflow 99 2 3 98) = [31, 102, 103] := by rfl

-- key_inst_arith_6
example : instToNumList (width := 8) (.arith (.addOverflow 99 2 3 98)) = [3, 31, 102, 103] := by rfl

-- key_arith_7
example : arithToNumList (width := 8) (.subOverflow 99 2 3 98) = [32, 102, 103] := by rfl

-- key_inst_arith_7
example : instToNumList (width := 8) (.arith (.subOverflow 99 2 3 98)) = [3, 32, 102, 103] := by rfl

-- key_fp_fpLess
example : instToNumList (width := 8) .skip = [1] := by rfl

-- key_mem_inst
example : instToNumList (width := 8) (.mem .load 99 (.addr 2 255)) = [1] := by rfl

end Flapjack.Test.WordCseInstructionKeysParity
