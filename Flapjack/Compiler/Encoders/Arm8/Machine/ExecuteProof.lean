import Flapjack.Compiler.Encoders.Arm8.Machine.Execute

/-!
# Fetching and decoding emitted ARMv8 bytes

These lemmas connect an encoded word to the 32-bit word fetched by `arm8Next`.
The caller supplies the fetch equation; the byte-level reassembly lemma is
kept separate because it is a future kernel proof obligation.
-/

namespace Flapjack.Compiler.Encoders.Arm8

/-- One `arm8Next` step executes the decoded instruction when the fetched word
is the instruction's encoding. -/
theorem arm8Next_encodeBytes (s : Arm8State) (i : Insn) (w : W)
    (_henc : encodeInsn i = some w)
    (hdec : decodeInsn w = some i)
    (hfetch : fetchWord s = w.setWidth 32) :
    arm8Next s = execInsn { s with pc := s.pc + 4 } i := by
  unfold arm8Next
  rw [hfetch]
  have hdec' : decodeInsn32 (w.setWidth 32) = some i := hdec
  rw [hdec']

/-- `noOp` decodes back to itself in the 64-bit carrier. -/
theorem decode_encode_noOp :
    decodeInsn ((encodeInsn .noOp).getD 0) = some .noOp := by
  decide

/-- `arm8Next` on the encoded `noOp` word only advances the PC. -/
theorem arm8Next_noOp (s : Arm8State)
    (hfetch : fetchWord s = ((encodeInsn .noOp).getD 0).setWidth 32) :
    arm8Next s = { s with pc := s.pc + 4 } := by
  have henc : encodeInsn .noOp = some ((encodeInsn .noOp).getD 0) := by
    unfold encodeInsn
    rfl
  rw [arm8Next_encodeBytes s .noOp ((encodeInsn .noOp).getD 0) henc decode_encode_noOp hfetch]
  rfl

end Flapjack.Compiler.Encoders.Arm8
