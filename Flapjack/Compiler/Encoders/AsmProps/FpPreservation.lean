import Flapjack.Compiler.Encoders.AsmSem.FpUpdates

/-! Original native FP field preservation; inherits the IEEE real rendering
of fpUpd (reals_as_rational_cuts, SOUNDNESS item 8). -/
namespace Flapjack.Compiler.Encoders.AsmProps
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem

@[hol "cakeml/compiler/encoders/asm/asmPropsScript.sml" "fp_upd_consts"
  (words_as_type_indexed_bitvec)]
theorem fpUpd_consts {width : Nat} [NeZero width] (operation : HolFp)
    (s : AsmState width) :
    (fpUpd operation s).memDomain = s.memDomain ∧
    (fpUpd operation s).align = s.align ∧
    (fpUpd operation s).mem = s.mem ∧
    (fpUpd operation s).lr = s.lr ∧
    (fpUpd operation s).be = s.be := by
  cases operation <;> dsimp [fpUpd, updReg, updFpReg, assertState]
  all_goals repeat first | rfl | constructor | split | (simp_all only [updReg, updFpReg, assertState]; done)

end Flapjack.Compiler.Encoders.AsmProps
