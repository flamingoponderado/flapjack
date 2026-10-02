import Flapjack.Compiler.Backend.StackLang.InstBuilders

/-! Kernel fixtures of original native helper constructors; no additional HOL theorem claimed. -/

namespace Flapjack.Test.StackLangInstBuilders

open Flapjack.Compiler.Backend.StackLang

-- move_1
example : moveInst (width := 1) 1234 42 =
    (.inst (.arith (.binop .or 1234 42 (.reg 42))) : HolProg 1) := by rfl

-- sub_inst_1
example : subInst (width := 1) 1234 42 =
    (.inst (.arith (.binop .sub 1234 1234 (.reg 42))) : HolProg 1) := by rfl

-- add_inst_1
example : addInst (width := 1) 1234 42 =
    (.inst (.arith (.binop .add 1234 1234 (.reg 42))) : HolProg 1) := by rfl

-- bytes_1
example : addBytesInWordInst (width := 1) 1234 =
    (.inst (.arith (.binop .add 1234 1234 (.imm (BitVec.ofNat 1 0)))) : HolProg 1) := by rfl

-- while_1
example : whileProg (width := 1) .notEqual 1234 (.imm 1) (.halt 42) =
    (.loop (.ite .notEqual 1234 (.imm 1) (.halt 42) (.break 0)) : HolProg 1) := by rfl

-- seq_1_0
example : listSeqHOL (width := 1) [] = (.skip : HolProg 1) := by rfl

-- seq_1_1
example : listSeqHOL (width := 1) [.halt 42] = (.halt 42 : HolProg 1) := by rfl

-- seq_1_2
example : listSeqHOL (width := 1) [.halt 42, .skip] = ((.seq (.halt 42) .skip) : HolProg 1) := by rfl

-- seq_1_3
example : listSeqHOL (width := 1) [.halt 42, .skip, .break 7] = ((.seq (.halt 42) (.seq .skip (.break 7))) : HolProg 1) := by rfl

-- move_8
example : moveInst (width := 8) 1234 42 =
    (.inst (.arith (.binop .or 1234 42 (.reg 42))) : HolProg 8) := by rfl

-- sub_inst_8
example : subInst (width := 8) 1234 42 =
    (.inst (.arith (.binop .sub 1234 1234 (.reg 42))) : HolProg 8) := by rfl

-- add_inst_8
example : addInst (width := 8) 1234 42 =
    (.inst (.arith (.binop .add 1234 1234 (.reg 42))) : HolProg 8) := by rfl

-- bytes_8
example : addBytesInWordInst (width := 8) 1234 =
    (.inst (.arith (.binop .add 1234 1234 (.imm (BitVec.ofNat 8 1)))) : HolProg 8) := by rfl

-- while_8
example : whileProg (width := 8) .notEqual 1234 (.imm 1) (.halt 42) =
    (.loop (.ite .notEqual 1234 (.imm 1) (.halt 42) (.break 0)) : HolProg 8) := by rfl

-- seq_8_0
example : listSeqHOL (width := 8) [] = (.skip : HolProg 8) := by rfl

-- seq_8_1
example : listSeqHOL (width := 8) [.halt 42] = (.halt 42 : HolProg 8) := by rfl

-- seq_8_2
example : listSeqHOL (width := 8) [.halt 42, .skip] = ((.seq (.halt 42) .skip) : HolProg 8) := by rfl

-- seq_8_3
example : listSeqHOL (width := 8) [.halt 42, .skip, .break 7] = ((.seq (.halt 42) (.seq .skip (.break 7))) : HolProg 8) := by rfl

-- move_32
example : moveInst (width := 32) 1234 42 =
    (.inst (.arith (.binop .or 1234 42 (.reg 42))) : HolProg 32) := by rfl

-- sub_inst_32
example : subInst (width := 32) 1234 42 =
    (.inst (.arith (.binop .sub 1234 1234 (.reg 42))) : HolProg 32) := by rfl

-- add_inst_32
example : addInst (width := 32) 1234 42 =
    (.inst (.arith (.binop .add 1234 1234 (.reg 42))) : HolProg 32) := by rfl

-- bytes_32
example : addBytesInWordInst (width := 32) 1234 =
    (.inst (.arith (.binop .add 1234 1234 (.imm (BitVec.ofNat 32 4)))) : HolProg 32) := by rfl

-- while_32
example : whileProg (width := 32) .notEqual 1234 (.imm 1) (.halt 42) =
    (.loop (.ite .notEqual 1234 (.imm 1) (.halt 42) (.break 0)) : HolProg 32) := by rfl

-- seq_32_0
example : listSeqHOL (width := 32) [] = (.skip : HolProg 32) := by rfl

-- seq_32_1
example : listSeqHOL (width := 32) [.halt 42] = (.halt 42 : HolProg 32) := by rfl

-- seq_32_2
example : listSeqHOL (width := 32) [.halt 42, .skip] = ((.seq (.halt 42) .skip) : HolProg 32) := by rfl

-- seq_32_3
example : listSeqHOL (width := 32) [.halt 42, .skip, .break 7] = ((.seq (.halt 42) (.seq .skip (.break 7))) : HolProg 32) := by rfl

-- move_64
example : moveInst (width := 64) 1234 42 =
    (.inst (.arith (.binop .or 1234 42 (.reg 42))) : HolProg 64) := by rfl

-- sub_inst_64
example : subInst (width := 64) 1234 42 =
    (.inst (.arith (.binop .sub 1234 1234 (.reg 42))) : HolProg 64) := by rfl

-- add_inst_64
example : addInst (width := 64) 1234 42 =
    (.inst (.arith (.binop .add 1234 1234 (.reg 42))) : HolProg 64) := by rfl

-- bytes_64
example : addBytesInWordInst (width := 64) 1234 =
    (.inst (.arith (.binop .add 1234 1234 (.imm (BitVec.ofNat 64 8)))) : HolProg 64) := by rfl

-- while_64
example : whileProg (width := 64) .notEqual 1234 (.imm 1) (.halt 42) =
    (.loop (.ite .notEqual 1234 (.imm 1) (.halt 42) (.break 0)) : HolProg 64) := by rfl

-- seq_64_0
example : listSeqHOL (width := 64) [] = (.skip : HolProg 64) := by rfl

-- seq_64_1
example : listSeqHOL (width := 64) [.halt 42] = (.halt 42 : HolProg 64) := by rfl

-- seq_64_2
example : listSeqHOL (width := 64) [.halt 42, .skip] = ((.seq (.halt 42) .skip) : HolProg 64) := by rfl

-- seq_64_3
example : listSeqHOL (width := 64) [.halt 42, .skip, .break 7] = ((.seq (.halt 42) (.seq .skip (.break 7))) : HolProg 64) := by rfl

-- move_80
example : moveInst (width := 80) 1234 42 =
    (.inst (.arith (.binop .or 1234 42 (.reg 42))) : HolProg 80) := by rfl

-- sub_inst_80
example : subInst (width := 80) 1234 42 =
    (.inst (.arith (.binop .sub 1234 1234 (.reg 42))) : HolProg 80) := by rfl

-- add_inst_80
example : addInst (width := 80) 1234 42 =
    (.inst (.arith (.binop .add 1234 1234 (.reg 42))) : HolProg 80) := by rfl

-- bytes_80
example : addBytesInWordInst (width := 80) 1234 =
    (.inst (.arith (.binop .add 1234 1234 (.imm (BitVec.ofNat 80 10)))) : HolProg 80) := by rfl

-- while_80
example : whileProg (width := 80) .notEqual 1234 (.imm 1) (.halt 42) =
    (.loop (.ite .notEqual 1234 (.imm 1) (.halt 42) (.break 0)) : HolProg 80) := by rfl

-- seq_80_0
example : listSeqHOL (width := 80) [] = (.skip : HolProg 80) := by rfl

-- seq_80_1
example : listSeqHOL (width := 80) [.halt 42] = (.halt 42 : HolProg 80) := by rfl

-- seq_80_2
example : listSeqHOL (width := 80) [.halt 42, .skip] = ((.seq (.halt 42) .skip) : HolProg 80) := by rfl

-- seq_80_3
example : listSeqHOL (width := 80) [.halt 42, .skip, .break 7] = ((.seq (.halt 42) (.seq .skip (.break 7))) : HolProg 80) := by rfl

-- Arbitrary native body/payload and list equations preserve the original polymorphic shape.

example {width : Nat} [NeZero width] (p q : HolProg width) (rest : List (HolProg width)) :
    listSeqHOL (p :: q :: rest) = .seq p (listSeqHOL (q :: rest)) := by rfl

end Flapjack.Test.StackLangInstBuilders
