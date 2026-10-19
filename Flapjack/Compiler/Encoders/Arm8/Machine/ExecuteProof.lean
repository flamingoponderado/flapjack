import Mathlib.Tactic.IntervalCases
import Flapjack.Compiler.Encoders.Arm8.Machine.Execute
import Flapjack.Misc.BytesInMemory

/-!
# Fetching and decoding emitted ARMv8 bytes

These lemmas connect the encoded byte list to the 32-bit word fetched by
`arm8Next`.  The reassembly proof is bit-by-bit over the four little-endian
bytes, so it stays within the kernel and needs no native decision procedure.
-/

namespace Flapjack.Compiler.Encoders.Arm8

open Flapjack

/-- Reassemble a 32-bit word from its four little-endian bytes. -/
theorem fetchWord_wordBytes (s : Arm8State) (w : W)
    (h0 : s.mem s.pc = w.extractLsb' 0 8)
    (h1 : s.mem (s.pc + 1) = w.extractLsb' 8 8)
    (h2 : s.mem (s.pc + 2) = w.extractLsb' 16 8)
    (h3 : s.mem (s.pc + 3) = w.extractLsb' 24 8) :
    fetchWord s = w.setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [fetchWord, h0, h1, h2, h3]
  simp
  interval_cases i <;> simp

/-- The four bytes of `encodeBytes i` reassemble to the encoding word. -/
theorem fetchWord_encodeBytes (s : Arm8State) (i : Insn) (w : W)
    (d : BitVec 64 → Prop) (henc : encodeInsn i = some w)
    (h : bytesInMemoryHOL s.pc (encodeBytes i) s.mem d) :
    fetchWord s = w.setWidth 32 := by
  simp only [encodeBytes, henc, wordBytes, bytesInMemoryHOL] at h
  rcases h with ⟨h0, _, h1, _, h2, _, h3, _⟩
  have h2' : s.mem (s.pc + 2) = w.extractLsb' 16 8 := by
    simpa [BitVec.add_assoc] using h2
  have h3' : s.mem (s.pc + 3) = w.extractLsb' 24 8 := by
    simpa [BitVec.add_assoc] using h3
  exact fetchWord_wordBytes s w h0 h1 h2' h3'

/-- One `arm8Next` step executes the decoded instruction when the fetched bytes
are its encoding. -/
theorem arm8Next_encodeBytes (s : Arm8State) (i : Insn) (w : W)
    (d : BitVec 64 → Prop) (henc : encodeInsn i = some w)
    (hdec : decodeInsn w = some i)
    (h : bytesInMemoryHOL s.pc (encodeBytes i) s.mem d) :
    arm8Next s = execInsn { s with pc := s.pc + 4 } i := by
  unfold arm8Next
  rw [fetchWord_encodeBytes s i w d henc h]
  have hdec' : decodeInsn32 (w.setWidth 32) = some i := hdec
  rw [hdec']

/-- `noOp` decodes back to itself in the 64-bit carrier. -/
theorem decode_encode_noOp :
    decodeInsn ((encodeInsn .noOp).getD 0) = some .noOp := by
  decide

/-- `arm8Next` on the encoding of `noOp` only advances the PC. -/
theorem arm8Next_noOp (s : Arm8State) (d : BitVec 64 → Prop)
    (h : bytesInMemoryHOL s.pc (encodeBytes .noOp) s.mem d) :
    arm8Next s = { s with pc := s.pc + 4 } := by
  have henc : encodeInsn .noOp = some ((encodeInsn .noOp).getD 0) := by
    unfold encodeInsn
    rfl
  rw [arm8Next_encodeBytes s .noOp ((encodeInsn .noOp).getD 0) d henc decode_encode_noOp h]
  rfl

end Flapjack.Compiler.Encoders.Arm8
