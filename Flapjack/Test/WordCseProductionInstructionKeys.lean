import Flapjack.RiscV.WordCse

/-! Source-shaped instruction-key observations at the actual CSE boundary.
Memory catch-all keys are distinct from load-fact keys. No simulation claim. -/
namespace Flapjack.Test.WordCseProductionInstructionKeys
open Flapjack Flapjack.RiscV

example {width : Nat} [NeZero width] (operator : WordMemOp) (destination base : Nat) :
    wordCseNativeInst? (.mem operator destination base : WordInst (BitVec width)) =
      some (.mem operator destination (.addr base 0)) := rfl

example {width : Nat} [NeZero width] (operator : WordMemOp) (destination base : Nat)
    (offset : BitVec width) :
    wordCseNativeInst? (.memOffset operator destination base offset) =
      some (.mem operator destination (.addr base offset)) := rfl

example {width : Nat} [NeZero width] (operator : WordMemOp) (destination base : Nat) :
    wordCseInstToNumList (.mem operator destination base : WordInst (BitVec width)) = [1] := rfl

example {width : Nat} [NeZero width] (operator : WordMemOp) (destination base : Nat)
    (offset : BitVec width) :
    wordCseInstToNumList (.memOffset operator destination base offset) = [1] := rfl

-- Diagnostic memory follows the same source catch-all, without truncating offsets.
example : wordCseInstToNumList (.memOffset .load32 99 2 (2 ^ 80 + 7) : WordInst Nat) = [1] := rfl

-- Source key_mem_inst; dedicated load keys remain separate.
example : wordCseInstToNumList (.memOffset .load 0 1 (0 : BitVec 8)) = [1] := rfl
example : wordCseLoadOffsetToNumList .load 1 (0 : BitVec 8) = [21,101,0] := rfl

-- Original key_const_1.
example : wordCseInstToNumList (.const 99 (-1 : BitVec 1)) = [2,1] := rfl

-- Original key_const_32.
example : wordCseInstToNumList (.const 99 (-1 : BitVec 32)) = [2,4294967295] := rfl

-- Original key_const_64.
example : wordCseInstToNumList (.const 99 (-1 : BitVec 64)) = [2,18446744073709551615] := rfl

-- Original key_const_80.
example : wordCseInstToNumList (.const 99 (-1 : BitVec 80)) = [2,1208925819614629174706175] := rfl

-- The distinct five-register extension is neither silently encoded as
-- source AddCarry nor confused with a source overflow instruction.
example {width : Nat} [NeZero width] (a b c d e : Nat) :
    wordCseNativeInst? (.arith (.addCarry a b c d e) : WordInst (BitVec width)) = none := rfl
example {width : Nat} [NeZero width] (a b c d e : Nat) :
    wordCseInstToNumList (.arith (.addCarry a b c d e) : WordInst (BitVec width)) = [3,31] := rfl

#print axioms wordCseInstToNumList_native
end Flapjack.Test.WordCseProductionInstructionKeys
