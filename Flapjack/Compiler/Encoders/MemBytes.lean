import Flapjack.Compiler.Encoders.AsmSem.Memory

/-!
# The little-endian byte bridge shared by the X64 and ARM8 memory cases

Both `encoder_correct` memory-case proofs identify the source's `readMemWord`
with the machine's `readMemN` byte reads.  `readBytes` is the little-endian word
of the bytes at `a`, `a + 1`, ..., and the lemmas below relate it to
`readMemWord` and spell out its OR-of-shifts form at the byte counts the two
lowerings use.  This is Flapjack infrastructure shared by the x86-64 and ARMv8
encoders; there is no separately named HOL original.
-/

namespace Flapjack.Compiler.Encoders

open Flapjack Compiler.Encoders.Asm Compiler.Encoders.AsmSem

/-- The little-endian value `readMemWord` assembles out of the bytes at `a`,
`a + 1`, `a + 2`, ... -/
def readBytes (mem : BitVec 64 → BitVec 8) (a : BitVec 64) : Nat → BitVec 64
  | 0 => 0
  | n + 1 => (readBytes mem (a + 1) n) <<< (8 : Nat) ||| (mem a).setWidth 64

/-- The numeral `0` of the word carrier is the empty word, so that the `BitVec`
zero lemmas apply to the base case of `readBytes`. -/
theorem zero64 : ((0 : BitVec 64) = 0#64) := rfl

/-- The value `readMemWord` assembles is the little-endian word of the bytes it
reads (`be = false`). -/
theorem readMemWord_fst (a : BitVec 64) (n : Nat) (s : AsmState 64) (hbe : s.be = false) :
    (readMemWord (resultWidth := 64) a n s).1 = readBytes s.mem a n := by
  induction n generalizing a s with
  | zero => simp [readMemWord, readBytes]
  | succ n ih =>
      rw [readMemWord_succ, hbe]
      simp only [Bool.false_eq_true, if_false]
      generalize hr : readMemWord (resultWidth := 64) (a + 1) n s = r
      obtain ⟨w, s1⟩ := r
      have hmem := readMemWord_mem_eq_direct (resultWidth := 64) (a + 1) n s
      rw [hr] at hmem
      have hw : w = readBytes s.mem (a + 1) n := by
        have h := ih (a + 1) s hbe
        rw [hr] at h
        exact h
      have hread : readMem a s1 = s.mem a := by
        have hmem' : s1.mem = s.mem := hmem
        simp only [readMem, hmem']
      rw [hw, hread]
      rfl

/-- The one-byte value of `readBytes`. -/
theorem readBytes_one (m : BitVec 64 → BitVec 8) (a : BitVec 64) :
    readBytes m a 1 = (m a).setWidth 64 := by
  simp [readBytes]

/-- The two-byte value of `readBytes`. -/
theorem readBytes_two (m : BitVec 64 → BitVec 8) (a : BitVec 64) :
    readBytes m a 2 = (m (a + 1)).setWidth 64 <<< (8 : Nat) ||| (m a).setWidth 64 := by
  simp [readBytes]

/-- The four-byte value of `readBytes`. -/
theorem readBytes_four (m : BitVec 64 → BitVec 8) (a : BitVec 64) :
    readBytes m a 4 = (m (a + 3)).setWidth 64 <<< (24 : Nat) |||
      (m (a + 2)).setWidth 64 <<< (16 : Nat) |||
      (m (a + 1)).setWidth 64 <<< (8 : Nat) ||| (m a).setWidth 64 := by
  simp only [readBytes, Nat.reduceAdd, zero64, BitVec.zero_shiftLeft, BitVec.zero_or,
    BitVec.shiftLeft_or_distrib, ← BitVec.shiftLeft_add, BitVec.or_assoc]
  rw [show a + 1 + 1 + 1 = a + 3 by bv_omega, show a + 1 + 1 = a + 2 by bv_omega]

/-- The eight-byte value of `readBytes`. -/
theorem readBytes_eight (m : BitVec 64 → BitVec 8) (a : BitVec 64) :
    readBytes m a 8 = (m (a + 7)).setWidth 64 <<< (56 : Nat) |||
      (m (a + 6)).setWidth 64 <<< (48 : Nat) |||
      (m (a + 5)).setWidth 64 <<< (40 : Nat) |||
      (m (a + 4)).setWidth 64 <<< (32 : Nat) |||
      (m (a + 3)).setWidth 64 <<< (24 : Nat) |||
      (m (a + 2)).setWidth 64 <<< (16 : Nat) |||
      (m (a + 1)).setWidth 64 <<< (8 : Nat) ||| (m a).setWidth 64 := by
  simp only [readBytes, Nat.reduceAdd, zero64, BitVec.zero_shiftLeft, BitVec.zero_or,
    BitVec.shiftLeft_or_distrib, ← BitVec.shiftLeft_add, BitVec.or_assoc]
  rw [show a + 1 + 1 + 1 + 1 + 1 + 1 + 1 = a + 7 by bv_omega,
    show a + 1 + 1 + 1 + 1 + 1 + 1 = a + 6 by bv_omega,
    show a + 1 + 1 + 1 + 1 + 1 = a + 5 by bv_omega,
    show a + 1 + 1 + 1 + 1 = a + 4 by bv_omega,
    show a + 1 + 1 + 1 = a + 3 by bv_omega,
    show a + 1 + 1 = a + 2 by bv_omega]

end Flapjack.Compiler.Encoders
