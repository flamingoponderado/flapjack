import Flapjack.Compiler.Encoders.AsmProps.Encoding

namespace Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack Flapjack.Compiler.Encoders.Asm

/-- Original local encoding nonemptiness lemma. Its asm_ok premise is retained
verbatim even though the enc_ok nonemptiness conjunct suffices for the proof. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem encOkNotEmpty {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (w : HolAsm width)
    (h : encOk c ∧ asmOkExact w c = true) : c.encode w ≠ [] := by
  intro hempty
  have hn := (h.1.2.1 w).2
  exact hn (by simp [hempty])

end Flapjack.Compiler.Backend.Semantics.TargetProps
