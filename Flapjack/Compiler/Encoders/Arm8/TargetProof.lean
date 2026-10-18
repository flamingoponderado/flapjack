import Flapjack.Compiler.Encoders.Arm8.Target

/-! Structural facts about the ARMv8 encoder.

`arm8_targetProofScript.sml` begins with length lemmas for `arm8_encode` and `arm8_enc`
(`length_arm8_encode`, `length_arm8_enc`, `arm8_encode_not_nil`, `arm8_encoding`) before
the state-transition proof of `arm8_encoder_correct`.  These are the corresponding facts
for Flapjack's encoder.  They are not tagged as exact HOL ports: HOL's lemmas range over
the full L3 `arm8$instruction` datatype, while `Insn` here is the subset that
`arm8_ast` emits, and `encodeBytes` replaces HOL's `arm8_encode` `BadCode` result with
its four zero bytes.

The main `arm8_encoder_correct` theorem is not ported: it needs the ARMv8 L3 machine
semantics (`arm8Script.sml` and `arm8_stepScript.sml`), which Flapjack does not yet
contain.  Source-to-assembly parity is checked instead by
`Flapjack/Test/Arm8Parity.lean`. -/
namespace Flapjack.Compiler.Encoders.Arm8

open Flapjack Compiler.Encoders.Asm Compiler.Encoders.AsmSem

/-- `arm8_encode` produces exactly four bytes for every instruction, including the
`BadCode` case (four zero bytes). -/
theorem length_encodeBytes (i : Insn) : (encodeBytes i).length = 4 := by
  unfold encodeBytes
  split <;> simp [wordBytes]

/-- `length_arm8_enc` for a list of lowered instructions. -/
theorem length_flatMap_encodeBytes (instructions : List Insn) :
    (instructions.flatMap encodeBytes).length = 4 * instructions.length := by
  induction instructions with
  | nil => simp
  | cons i rest ih =>
      simp only [List.flatMap_cons, List.length_append, length_encodeBytes, ih,
        List.length_cons, Nat.mul_succ]
      omega

/-- `length_arm8_enc`: the lowered byte sequence has length four times the number of
lowered instructions. -/
theorem length_arm8Enc (instruction : HolAsm 64) :
    (arm8Enc instruction).length = 4 * (arm8Ast instruction).length := by
  rw [arm8Enc]
  exact length_flatMap_encodeBytes _

/-- `arm8_encode_not_nil`: every instruction encodes to a nonempty byte list. -/
theorem encodeBytes_not_nil (i : Insn) : encodeBytes i ≠ [] := by
  intro empty
  have length := length_encodeBytes i
  rw [empty] at length
  simp at length

end Flapjack.Compiler.Encoders.Arm8
