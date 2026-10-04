import Flapjack.Compiler.Backend.LabToTarget.NopEncoding
import Flapjack.Compiler.Backend.LabToTarget.Padding
import Flapjack.Misc.TakeFlatReplicate
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Encoders.Asm Flapjack.Misc

/-- The source's encoded-element carrier remains independent of its word dimension. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem encWithNop_padBytes_length {width : Nat} [NeZero width] {Value : Type}
    (enc : HolAsm width → List Value) (x : HolAsm width) :
    encWithNop enc x (padBytes (enc x) (enc x).length (enc (.inst .skip))) := by
  rw [encWithNop_iff]
  exact ⟨0, by simp [padBytes]⟩

/-- All original NOP identity, bound, divisibility and positivity guards are retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem encWithNop_padBytes {width : Nat} [NeZero width] {Value : Type}
    (nop : List Value) (enc : HolAsm width → List Value) (x : HolAsm width) (len : Nat) :
    nop = enc (.inst .skip) ∧ (enc x).length ≤ len ∧
      (enc x).length % nop.length = 0 ∧ len % nop.length = 0 ∧ 0 < nop.length →
    encWithNop enc x (padBytes (enc x) len nop) := by
  rintro ⟨hnop, hbound, hencmod, hlenmod, hpos⟩
  rw [encWithNop_iff]
  by_cases heq : len ≤ (enc x).length
  · have hl : len = (enc x).length := by omega
    exact ⟨0, by simp [padBytes,hl]⟩
  · have ha : (enc x).length / nop.length * nop.length = (enc x).length := by
      simpa [hencmod, Nat.mul_comm] using Nat.mod_add_div (enc x).length nop.length
    have hz : len / nop.length * nop.length = len := by
      simpa [hlenmod, Nat.mul_comm] using Nat.mod_add_div len nop.length
    have hdiff : (len / nop.length - (enc x).length / nop.length) * nop.length =
        len - (enc x).length := by rw [Nat.sub_mul, hz, ha]
    have hk : len / nop.length - (enc x).length / nop.length ≤ len :=
      Nat.le_trans (Nat.sub_le _ _) (Nat.div_le_self _ _)
    have ht := takeFlatReplicateLeq len (len / nop.length - (enc x).length / nop.length)
      nop nop.length ⟨rfl,hk⟩
    have hb : (enc x).take len = enc x := List.take_of_length_le hbound
    refine ⟨len / nop.length - (enc x).length / nop.length, ?_⟩
    simpa [padBytes,heq,List.take_append,hb,← hdiff,hnop] using
      congrArg (List.append (enc x)) ht
end Flapjack.Compiler.Backend.LabToTarget
