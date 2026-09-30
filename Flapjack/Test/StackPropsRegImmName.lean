import Flapjack.Compiler.Backend.StackProps.RegisterNames
namespace Flapjack.Test.StackPropsRegImmName
open Flapjack.Compiler.Backend.StackProps Flapjack.Compiler.Encoders.Asm
example {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (op : Sum BinOp Cmp) (r : Nat) :
    regImmName op (.reg r) c ↔ r < c.regCount - c.avoidRegs.length := Iff.rfl
example {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (op : Sum BinOp Cmp) (v : BitVec width) :
    regImmName op (.imm v) c ↔ c.validImm op v = true := Iff.rfl
example {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (h : c.validImm (.inl .xor) (-1 : BitVec width) = false) :
    ¬ regImmName (.inl .xor) (.imm (-1 : BitVec width)) c := by
  change ¬ c.validImm (.inl .xor) (-1 : BitVec width) = true
  rw [h]
  decide
example {width : Nat} [NeZero width] (c : AsmConfigExact width) :
    asmRegImmOkExact (.inl .xor) (.imm (-1 : BitVec width)) c = true := by
  simp only [asmRegImmOkExact, Bool.or_eq_true, Bool.and_eq_true]
  left
  constructor
  · decide
  · simp
end Flapjack.Test.StackPropsRegImmName
