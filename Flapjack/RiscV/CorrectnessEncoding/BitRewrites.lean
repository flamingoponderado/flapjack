import Flapjack.RiscV.L3.Step.BitRewrites
/-! Exact full word64 rewrites used by the original target encoder proof. -/
namespace Flapjack.RiscV.TargetProof
/-- The eight original word64 PC increments preserve bit zero. -/
theorem word_bit_0_add4 (w : BitVec 64) :
    (w + 4#64).getLsbD 0 = w.getLsbD 0 ∧
    (w + 8#64).getLsbD 0 = w.getLsbD 0 ∧
    (w + 12#64).getLsbD 0 = w.getLsbD 0 ∧
    (w + 16#64).getLsbD 0 = w.getLsbD 0 ∧
    (w + 20#64).getLsbD 0 = w.getLsbD 0 ∧
    (w + 24#64).getLsbD 0 = w.getLsbD 0 ∧
    (w + 28#64).getLsbD 0 = w.getLsbD 0 ∧
    (w + 32#64).getLsbD 0 = w.getLsbD 0 := by
  simp only [BitVec.getLsbD_add (by decide : 0 < 64), BitVec.carry_zero]
  simp
/-- Clearing word64 bit zero makes its masked sum inherit the other operand bit. -/
theorem word_bit_0_lemmas (w v : BitVec 64) :
    (0xFFFFFFFFFFFFFFFE#64 &&& w).getLsbD 0 = false ∧
    ((0xFFFFFFFFFFFFFFFE#64 &&& w) + v).getLsbD 0 = v.getLsbD 0 :=
  Flapjack.RiscV.L3.Step.word_bit_0_lemmas w v
end Flapjack.RiscV.TargetProof
