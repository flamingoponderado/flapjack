import Flapjack.Compiler.Encoders.AsmSem.Arithmetic

/-! Full original ASM PC and arithmetic update invariants. The statements retain
all original conjuncts over the native state and positive word dimension. -/
namespace Flapjack.Compiler.Encoders.AsmProps
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem

@[hol "cakeml/compiler/encoders/asm/asmPropsScript.sml" "upd_pc_simps"
  (words_as_type_indexed_bitvec)]
theorem updPc_simps {width : Nat} [NeZero width] (x : BitVec width)
    (s : AsmState width) :
    (updPc x s).align = s.align ∧
    (updPc x s).memDomain = s.memDomain ∧
    (updPc x s).failed = s.failed ∧
    (updPc x s).be = s.be ∧
    (updPc x s).mem = s.mem ∧
    (updPc x s).regs = s.regs ∧
    (updPc x s).fpRegs = s.fpRegs ∧
    (updPc x s).lr = s.lr ∧
    (updPc x s).pc = x := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

@[hol "cakeml/compiler/encoders/asm/asmPropsScript.sml" "binop_upd_consts"
  (words_as_type_indexed_bitvec)]
theorem binopUpd_consts {width : Nat} [NeZero width] (a : Nat) (b : HolBinop)
    (c d : BitVec width) (x : AsmState width) :
    (binopUpd a b c d x).memDomain = x.memDomain ∧
    (binopUpd a b c d x).align = x.align ∧
    (binopUpd a b c d x).failed = x.failed ∧
    (binopUpd a b c d x).mem = x.mem ∧
    (binopUpd a b c d x).lr = x.lr ∧
    (binopUpd a b c d x).be = x.be := by
  cases b <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

@[hol "cakeml/compiler/encoders/asm/asmPropsScript.sml" "arith_upd_consts"
  (words_as_type_indexed_bitvec)]
theorem arithUpd_consts {width : Nat} [NeZero width] (a : HolArith width)
    (x : AsmState width) :
    (arithUpd a x).memDomain = x.memDomain ∧
    (arithUpd a x).align = x.align ∧
    (arithUpd a x).mem = x.mem ∧
    (arithUpd a x).lr = x.lr ∧
    (arithUpd a x).be = x.be := by
  cases a <;> simp [arithUpd, binopUpd, updReg, assertState]

end Flapjack.Compiler.Encoders.AsmProps
