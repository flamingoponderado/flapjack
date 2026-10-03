import Flapjack.RiscV.WordCse

/-! Same-input original instruction-key observations at the actual executed
CSE call sites. Overflow and FP native rows have no production carrier and are
outside this routing slice; the five-register extension is explicitly separate. -/
namespace Flapjack.Test.WordCseProductionArithmeticKeys
open Flapjack Flapjack.RiscV

-- Original key_arith_0 / key_inst_arith_0.
example : wordCseArithToNumList (.binOp .add 99 2 (.reg 3) : WordArith (BitVec 8)) = [25,35,102,33,103] := by rfl
example : wordCseInstToNumList (.arith (.binOp .add 99 2 (.reg 3) : WordArith (BitVec 8))) = 3 :: [25,35,102,33,103] := by rfl

-- Original key_arith_1 / key_inst_arith_1.
example : wordCseArithToNumList (.longMul 99 98 2 3 : WordArith (BitVec 8)) = [26,102,103] := by rfl
example : wordCseInstToNumList (.arith (.longMul 99 98 2 3 : WordArith (BitVec 8))) = 3 :: [26,102,103] := by rfl

-- Original key_arith_2 / key_inst_arith_2.
example : wordCseArithToNumList (.longDiv 99 98 2 3 4 : WordArith (BitVec 8)) = [27,102,103,104] := by rfl
example : wordCseInstToNumList (.arith (.longDiv 99 98 2 3 4 : WordArith (BitVec 8))) = 3 :: [27,102,103,104] := by rfl

-- Original key_arith_3 / key_inst_arith_3.
example : wordCseArithToNumList (.shift .ror 99 2 (.imm 255) : WordArith (BitVec 8)) = [28,43,102,34,255] := by rfl
example : wordCseInstToNumList (.arith (.shift .ror 99 2 (.imm 255) : WordArith (BitVec 8))) = 3 :: [28,43,102,34,255] := by rfl

-- Original key_arith_4 / key_inst_arith_4.
example : wordCseArithToNumList (.div 99 2 3 : WordArith (BitVec 8)) = [29,102,103] := by rfl
example : wordCseInstToNumList (.arith (.div 99 2 3 : WordArith (BitVec 8))) = 3 :: [29,102,103] := by rfl

-- Original key_arith_5 / key_inst_arith_5.
example : wordCseArithToNumList (.cakeAddCarry 99 2 3 98 : WordArith (BitVec 8)) = [30,102,103] := by rfl
example : wordCseInstToNumList (.arith (.cakeAddCarry 99 2 3 98 : WordArith (BitVec 8))) = 3 :: [30,102,103] := by rfl

-- The full successful-codec correspondence is width-polymorphic and requires
-- no unique registers or immediate range hypothesis.
example {width : Nat} [NeZero width]
    (operation : WordArith (BitVec width)) (native : Compiler.Encoders.Asm.HolArith width)
    (converted : Compiler.Backend.StackToLab.ExecutedCodec.arithFromExecuted? operation = some native) :
    wordCseInstToNumList (.arith operation) = Compiler.Backend.WordCse.instToNumList (.arith native) := by
  apply wordCseInstToNumList_native
  simp [wordCseNativeInst?, Compiler.Backend.StackToLab.ExecutedCodec.instFromExecuted?, converted]

-- The unsupported five-register primitive never receives an invented native key.
example {width : Nat} [NeZero width] (a b c d e : Nat) :
    wordCseArithToNumList (.addCarry a b c d e : WordArith (BitVec width)) = [31] := by rfl

-- Generic diagnostic immediates retain their unbounded values.
example : wordCseArithToNumList (.binOp .add 99 2 (.imm (2 ^ 80 + 7)) : WordArith Nat) =
    [25,35,102,34,2 ^ 80 + 7] := by rfl

#print axioms wordCseArithToNumList_native
end Flapjack.Test.WordCseProductionArithmeticKeys
