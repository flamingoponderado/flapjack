import Flapjack.Compiler.Backend.WordToStack.ProductionThreeToTwoDomain

namespace Flapjack.Test.ProductionThreeToTwoDomain
open Flapjack Flapjack.RiscV
/-! Kernel regressions for the actual production transform and codec domain.
These are Flapjack-only checks, not original HOL three-to-two output claims.
The production Assign rewrites and nonreturning-handler traversal are tested
as implemented; native pass equality and compiler correctness remain open. -/
-- skip
example : (wordLangProgToHOL (wordThreeToTwoReg (.skip : WordProg (BitVec 64)))).isSome = true := by decide +kernel
example : (wordLangProgToHOL (.skip : WordProg (BitVec 64))).isSome = true := by decide +kernel
-- move
example : (wordLangProgToHOL (wordThreeToTwoReg (.move 9 [(1,2),(1,2)] : WordProg (BitVec 64)))).isSome = true := by decide +kernel
example : (wordLangProgToHOL (.move 9 [(1,2),(1,2)] : WordProg (BitVec 64))).isSome = true := by decide +kernel
-- constant
example : (wordLangProgToHOL (wordThreeToTwoReg (.inst (.const 3 7) : WordProg (BitVec 64)))).isSome = true := by decide +kernel
example : (wordLangProgToHOL (.inst (.const 3 7) : WordProg (BitVec 64))).isSome = true := by decide +kernel
-- source_carry
example : (wordLangProgToHOL (wordThreeToTwoReg (.inst (.arith (.cakeAddCarry 1 2 3 4)) : WordProg (BitVec 64)))).isSome = true := by decide +kernel
example : (wordLangProgToHOL (.inst (.arith (.cakeAddCarry 1 2 3 4)) : WordProg (BitVec 64))).isSome = true := by decide +kernel
-- five_carry
example : (wordLangProgToHOL (wordThreeToTwoReg (.inst (.arith (.addCarry 1 2 3 4 5)) : WordProg (BitVec 64)))).isSome = false := by decide +kernel
example : (wordLangProgToHOL (.inst (.arith (.addCarry 1 2 3 4 5)) : WordProg (BitVec 64))).isSome = false := by decide +kernel
-- load16
example : (wordLangProgToHOL (wordThreeToTwoReg (.inst (.mem .load16 2 4) : WordProg (BitVec 64)))).isSome = true := by decide +kernel
example : (wordLangProgToHOL (.inst (.mem .load16 2 4) : WordProg (BitVec 64))).isSome = true := by decide +kernel
-- store16_offset
example : (wordLangProgToHOL (wordThreeToTwoReg (.inst (.memOffset .store16 2 4 8) : WordProg (BitVec 64)))).isSome = true := by decide +kernel
example : (wordLangProgToHOL (.inst (.memOffset .store16 2 4 8) : WordProg (BitVec 64))).isSome = true := by decide +kernel
-- get
example : (wordLangProgToHOL (wordThreeToTwoReg (.get 3 .globals : WordProg (BitVec 64)))).isSome = true := by decide +kernel
example : (wordLangProgToHOL (.get 3 .globals : WordProg (BitVec 64))).isSome = true := by decide +kernel
-- set
example : (wordLangProgToHOL (wordThreeToTwoReg (.set .globals (.var 7) : WordProg (BitVec 64)))).isSome = true := by decide +kernel
example : (wordLangProgToHOL (.set .globals (.var 7) : WordProg (BitVec 64))).isSome = true := by decide +kernel
-- constants
example : (wordLangProgToHOL (wordThreeToTwoReg (.storeConsts 1 2 3 4 [(true,7),(false,9)] : WordProg (BitVec 64)))).isSome = true := by decide +kernel
example : (wordLangProgToHOL (.storeConsts 1 2 3 4 [(true,7),(false,9)] : WordProg (BitVec 64))).isSome = true := by decide +kernel
-- heap
example : (wordLangProgToHOL (wordThreeToTwoReg (.opCurrHeap .add 3 4 : WordProg (BitVec 64)))).isSome = true := by decide +kernel
example : (wordLangProgToHOL (.opCurrHeap .add 3 4 : WordProg (BitVec 64))).isSome = true := by decide +kernel
-- install
example : (wordLangProgToHOL (wordThreeToTwoReg (.install 1 2 3 4 ([5],[6]) : WordProg (BitVec 64)))).isSome = true := by decide +kernel
example : (wordLangProgToHOL (.install 1 2 3 4 ([5],[6]) : WordProg (BitVec 64))).isSome = true := by decide +kernel
-- ffi
example : (wordLangProgToHOL (wordThreeToTwoReg (.ffi "domain" 1 2 3 4 ([5],[6]) : WordProg (BitVec 64)))).isSome = true := by decide +kernel
example : (wordLangProgToHOL (.ffi "domain" 1 2 3 4 ([5],[6]) : WordProg (BitVec 64))).isSome = true := by decide +kernel
-- store
example : (wordLangProgToHOL (wordThreeToTwoReg (.store (.var 3) 7 : WordProg (BitVec 64)))).isSome = true := by decide +kernel
example : (wordLangProgToHOL (.store (.var 3) 7 : WordProg (BitVec 64))).isSome = true := by decide +kernel
-- allocate
example : (wordLangProgToHOL (wordThreeToTwoReg (.alloc 3 ([1,1],[2,3]) : WordProg (BitVec 64)))).isSome = true := by decide +kernel
example : (wordLangProgToHOL (.alloc 3 ([1,1],[2,3]) : WordProg (BitVec 64))).isSome = true := by decide +kernel
-- raise
example : (wordLangProgToHOL (wordThreeToTwoReg (.raise 7 : WordProg (BitVec 64)))).isSome = true := by decide +kernel
example : (wordLangProgToHOL (.raise 7 : WordProg (BitVec 64))).isSome = true := by decide +kernel
-- return
example : (wordLangProgToHOL (wordThreeToTwoReg (.return 11 [2,3] : WordProg (BitVec 64)))).isSome = true := by decide +kernel
example : (wordLangProgToHOL (.return 11 [2,3] : WordProg (BitVec 64))).isSome = true := by decide +kernel
-- break
example : (wordLangProgToHOL (wordThreeToTwoReg (.break 2 : WordProg (BitVec 64)))).isSome = true := by decide +kernel
example : (wordLangProgToHOL (.break 2 : WordProg (BitVec 64))).isSome = true := by decide +kernel
-- continue
example : (wordLangProgToHOL (wordThreeToTwoReg (.continue 3 : WordProg (BitVec 64)))).isSome = true := by decide +kernel
example : (wordLangProgToHOL (.continue 3 : WordProg (BitVec 64))).isSome = true := by decide +kernel
-- tick
example : (wordLangProgToHOL (wordThreeToTwoReg (.tick : WordProg (BitVec 64)))).isSome = true := by decide +kernel
example : (wordLangProgToHOL (.tick : WordProg (BitVec 64))).isSome = true := by decide +kernel
-- location
example : (wordLangProgToHOL (wordThreeToTwoReg (.locValue 3 9 : WordProg (BitVec 64)))).isSome = true := by decide +kernel
example : (wordLangProgToHOL (.locValue 3 9 : WordProg (BitVec 64))).isSome = true := by decide +kernel
-- code_write
example : (wordLangProgToHOL (wordThreeToTwoReg (.codeBufferWrite 3 4 : WordProg (BitVec 64)))).isSome = true := by decide +kernel
example : (wordLangProgToHOL (.codeBufferWrite 3 4 : WordProg (BitVec 64))).isSome = true := by decide +kernel
-- data_write
example : (wordLangProgToHOL (wordThreeToTwoReg (.dataBufferWrite 3 4 : WordProg (BitVec 64)))).isSome = true := by decide +kernel
example : (wordLangProgToHOL (.dataBufferWrite 3 4 : WordProg (BitVec 64))).isSome = true := by decide +kernel
-- shared
example : (wordLangProgToHOL (wordThreeToTwoReg (.shareInst .load16 3 (.var 9) : WordProg (BitVec 64)))).isSome = true := by decide +kernel
example : (wordLangProgToHOL (.shareInst .load16 3 (.var 9) : WordProg (BitVec 64))).isSome = true := by decide +kernel
-- assign_one
example : (wordLangProgToHOL (wordThreeToTwoReg (.assign 10 (.op .add [.var 20]) : WordProg (BitVec 64)))).isSome = true := by decide +kernel
example : (wordLangProgToHOL (.assign 10 (.op .add [.var 20]) : WordProg (BitVec 64))).isSome = true := by decide +kernel
-- assign_constant_first
example : (wordLangProgToHOL (wordThreeToTwoReg (.assign 10 (.op .add [.const 7,.var 20]) : WordProg (BitVec 64)))).isSome = true := by decide +kernel
example : (wordLangProgToHOL (.assign 10 (.op .add [.const 7,.var 20]) : WordProg (BitVec 64))).isSome = true := by decide +kernel
-- assign_var_const
example : (wordLangProgToHOL (wordThreeToTwoReg (.assign 10 (.op .add [.var 20,.const 7]) : WordProg (BitVec 64)))).isSome = true := by decide +kernel
example : (wordLangProgToHOL (.assign 10 (.op .add [.var 20,.const 7]) : WordProg (BitVec 64))).isSome = true := by decide +kernel
-- assign_var_var
example : (wordLangProgToHOL (wordThreeToTwoReg (.assign 30 (.op .sub [.var 40,.var 50]) : WordProg (BitVec 64)))).isSome = true := by decide +kernel
example : (wordLangProgToHOL (.assign 30 (.op .sub [.var 40,.var 50]) : WordProg (BitVec 64))).isSome = true := by decide +kernel
-- sequence
example : (wordLangProgToHOL (wordThreeToTwoReg (.seq (.assign 10 (.op .add [.var 20,.const 7])) (.assign 30 (.op .sub [.var 40,.var 50])) : WordProg (BitVec 64)))).isSome = true := by decide +kernel
example : (wordLangProgToHOL (.seq (.assign 10 (.op .add [.var 20,.const 7])) (.assign 30 (.op .sub [.var 40,.var 50])) : WordProg (BitVec 64))).isSome = true := by decide +kernel
-- sequence_rejected
example : (wordLangProgToHOL (wordThreeToTwoReg (.seq (.assign 10 (.op .add [.var 20,.const 7])) (.inst (.arith (.addCarry 1 2 3 4 5))) : WordProg (BitVec 64)))).isSome = false := by decide +kernel
example : (wordLangProgToHOL (.seq (.assign 10 (.op .add [.var 20,.const 7])) (.inst (.arith (.addCarry 1 2 3 4 5))) : WordProg (BitVec 64))).isSome = false := by decide +kernel
-- conditional
example : (wordLangProgToHOL (wordThreeToTwoReg (.ite .equal 3 (.imm 7) (.assign 10 (.op .add [.var 20,.const 7])) (.assign 30 (.op .sub [.var 40,.var 50])) : WordProg (BitVec 64)))).isSome = true := by decide +kernel
example : (wordLangProgToHOL (.ite .equal 3 (.imm 7) (.assign 10 (.op .add [.var 20,.const 7])) (.assign 30 (.op .sub [.var 40,.var 50])) : WordProg (BitVec 64))).isSome = true := by decide +kernel
-- conditional_rejected
example : (wordLangProgToHOL (wordThreeToTwoReg (.ite .equal 3 (.imm 7) (.assign 10 (.op .add [.var 20,.const 7])) (.inst (.arith (.addCarry 1 2 3 4 5))) : WordProg (BitVec 64)))).isSome = false := by decide +kernel
example : (wordLangProgToHOL (.ite .equal 3 (.imm 7) (.assign 10 (.op .add [.var 20,.const 7])) (.inst (.arith (.addCarry 1 2 3 4 5))) : WordProg (BitVec 64))).isSome = false := by decide +kernel
-- loop
example : (wordLangProgToHOL (wordThreeToTwoReg (.loop [1,2] (.assign 10 (.op .add [.var 20,.const 7])) [3,4] : WordProg (BitVec 64)))).isSome = true := by decide +kernel
example : (wordLangProgToHOL (.loop [1,2] (.assign 10 (.op .add [.var 20,.const 7])) [3,4] : WordProg (BitVec 64))).isSome = true := by decide +kernel
-- loop_rejected
example : (wordLangProgToHOL (wordThreeToTwoReg (.loop [] (.inst (.arith (.addCarry 1 2 3 4 5))) [] : WordProg (BitVec 64)))).isSome = false := by decide +kernel
example : (wordLangProgToHOL (.loop [] (.inst (.arith (.addCarry 1 2 3 4 5))) [] : WordProg (BitVec 64))).isSome = false := by decide +kernel
-- must_terminate
example : (wordLangProgToHOL (wordThreeToTwoReg (.mustTerminate (.assign 30 (.op .sub [.var 40,.var 50])) : WordProg (BitVec 64)))).isSome = true := by decide +kernel
example : (wordLangProgToHOL (.mustTerminate (.assign 30 (.op .sub [.var 40,.var 50])) : WordProg (BitVec 64))).isSome = true := by decide +kernel
-- must_terminate_rejected
example : (wordLangProgToHOL (wordThreeToTwoReg (.mustTerminate (.inst (.arith (.addCarry 1 2 3 4 5))) : WordProg (BitVec 64)))).isSome = false := by decide +kernel
example : (wordLangProgToHOL (.mustTerminate (.inst (.arith (.addCarry 1 2 3 4 5))) : WordProg (BitVec 64))).isSome = false := by decide +kernel
-- tail_none
example : (wordLangProgToHOL (wordThreeToTwoReg (.call none none [] none : WordProg (BitVec 64)))).isSome = true := by decide +kernel
example : (wordLangProgToHOL (.call none none [] none : WordProg (BitVec 64))).isSome = true := by decide +kernel
-- tail_handler
example : (wordLangProgToHOL (wordThreeToTwoReg (.call none (some 9) [1,2] (some (7,(.assign 10 (.op .add [.var 20,.const 7])),11,12)) : WordProg (BitVec 64)))).isSome = true := by decide +kernel
example : (wordLangProgToHOL (.call none (some 9) [1,2] (some (7,(.assign 10 (.op .add [.var 20,.const 7])),11,12)) : WordProg (BitVec 64))).isSome = true := by decide +kernel
-- tail_handler_rejected
example : (wordLangProgToHOL (wordThreeToTwoReg (.call none none [] (some (7,(.inst (.arith (.addCarry 1 2 3 4 5))),11,12)) : WordProg (BitVec 64)))).isSome = false := by decide +kernel
example : (wordLangProgToHOL (.call none none [] (some (7,(.inst (.arith (.addCarry 1 2 3 4 5))),11,12)) : WordProg (BitVec 64))).isSome = false := by decide +kernel
-- return_none
example : (wordLangProgToHOL (wordThreeToTwoReg (.call (some ([2],([3],[4]),(.assign 10 (.op .add [.var 20,.const 7])),11,12)) none [1] none : WordProg (BitVec 64)))).isSome = true := by decide +kernel
example : (wordLangProgToHOL (.call (some ([2],([3],[4]),(.assign 10 (.op .add [.var 20,.const 7])),11,12)) none [1] none : WordProg (BitVec 64))).isSome = true := by decide +kernel
-- return_handler
example : (wordLangProgToHOL (wordThreeToTwoReg (.call (some ([2],([3],[4]),(.assign 10 (.op .add [.var 20,.const 7])),11,12)) (some 9) [1] (some (7,(.assign 30 (.op .sub [.var 40,.var 50])),13,14)) : WordProg (BitVec 64)))).isSome = true := by decide +kernel
example : (wordLangProgToHOL (.call (some ([2],([3],[4]),(.assign 10 (.op .add [.var 20,.const 7])),11,12)) (some 9) [1] (some (7,(.assign 30 (.op .sub [.var 40,.var 50])),13,14)) : WordProg (BitVec 64))).isSome = true := by decide +kernel
-- return_body_rejected
example : (wordLangProgToHOL (wordThreeToTwoReg (.call (some ([2],([],[]),(.inst (.arith (.addCarry 1 2 3 4 5))),11,12)) none [] (some (7,(.assign 10 (.op .add [.var 20,.const 7])),13,14)) : WordProg (BitVec 64)))).isSome = false := by decide +kernel
example : (wordLangProgToHOL (.call (some ([2],([],[]),(.inst (.arith (.addCarry 1 2 3 4 5))),11,12)) none [] (some (7,(.assign 10 (.op .add [.var 20,.const 7])),13,14)) : WordProg (BitVec 64))).isSome = false := by decide +kernel
-- return_handler_rejected
example : (wordLangProgToHOL (wordThreeToTwoReg (.call (some ([2],([],[]),(.assign 10 (.op .add [.var 20,.const 7])),11,12)) none [] (some (7,(.inst (.arith (.addCarry 1 2 3 4 5))),13,14)) : WordProg (BitVec 64)))).isSome = false := by decide +kernel
example : (wordLangProgToHOL (.call (some ([2],([],[]),(.assign 10 (.op .add [.var 20,.const 7])),11,12)) none [] (some (7,(.inst (.arith (.addCarry 1 2 3 4 5))),13,14)) : WordProg (BitVec 64))).isSome = false := by decide +kernel
example : wordThreeToTwoReg (.assign 10 (.op .add [.var 20,.const 7]) : WordProg (BitVec 64)) = .seq (.move 0 [(10,20)]) (.assign 10 (.op .add [.var 10,.const 7])) := by simp [wordThreeToTwoReg]
example : wordThreeToTwoReg (.assign 30 (.op .sub [.var 40,.var 50]) : WordProg (BitVec 64)) = .seq (.move 0 [(30,40)]) (.assign 30 (.op .sub [.var 30,.var 50])) := by simp [wordThreeToTwoReg]
example {width : Nat} (program : WordProg (BitVec width)) :
    (wordLangProgToHOL (wordThreeToTwoReg program)).isSome =
      (wordLangProgToHOL program).isSome :=
  wordLangProgToHOL_wordThreeToTwoReg_isSome program
-- The actual nonreturning Call still transforms its handler.
example : wordThreeToTwoReg
    (.call none (some 9) [1,2]
      (some (7, .assign 10 (.op .add [.var 20,.const 7]),11,12)) :
      WordProg (BitVec 64)) =
    .call none (some 9) [1,2]
      (some (7, .seq (.move 0 [(10,20)])
        (.assign 10 (.op .add [.var 10,.const 7])),11,12)) := by
  simp [wordThreeToTwoReg]

-- Returning Call transforms both bodies and preserves all metadata.
example : wordThreeToTwoReg
    (.call (some ([2],([3],[4]),
      .assign 10 (.op .add [.var 20,.const 7]),11,12))
      (some 9) [1] (some (7,
        .assign 30 (.op .sub [.var 40,.var 50]),13,14)) : WordProg (BitVec 64)) =
    .call (some ([2],([3],[4]),
      .seq (.move 0 [(10,20)]) (.assign 10 (.op .add [.var 10,.const 7])),11,12))
      (some 9) [1] (some (7,
        .seq (.move 0 [(30,40)]) (.assign 30 (.op .sub [.var 30,.var 50])),13,14)) := by
  simp [wordThreeToTwoReg]

end Flapjack.Test.ProductionThreeToTwoDomain
