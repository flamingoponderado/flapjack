import Flapjack.Compiler.Encoders.Mips32.Target

/-! Byte-level facts about Ziren's association-list memory `ZirenDet.Isa.Mem`. -/

namespace Flapjack.Mips32.TargetProof
open ZirenDet.Isa Flapjack.Mips32

theorem find?_filter_ne (l : List (W × BitVec 8)) (a x : W) (h : x ≠ a) :
    (l.filter (fun p => p.1 != a)).find? (fun p => p.1 == x) = l.find? (fun p => p.1 == x) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    by_cases hp : p.1 = a
    · have hx : (a == x) = false := by simp [Ne.symm h]
      simp [hp, hx, ih]
    · simp only [List.filter_cons, bne_iff_ne, ne_eq, hp, not_false_eq_true, ↓reduceIte,
        List.find?_cons]
      split <;> simp_all

@[simp] theorem readByte_writeByte (m : Mem) (a x : W) (b : BitVec 8) :
    (m.writeByte a b).readByte x = if x = a then b else m.readByte x := by
  unfold Mem.readByte Mem.writeByte
  by_cases h : x = a
  · subst h; simp
  · have hx : ((a, b).1 == x) = false := by simp [Ne.symm h]
    simp only [List.find?_cons, hx, h, ↓reduceIte]
    rw [find?_filter_ne _ _ _ h]

theorem readWord_eq (m : Mem) (a : W) :
    m.readWord a = m.readByte (a + 3) ++ m.readByte (a + 2) ++ m.readByte (a + 1) ++ m.readByte a :=
  rfl

theorem readHalf_eq (m : Mem) (a : W) : m.readHalf a = m.readByte (a + 1) ++ m.readByte a := rfl

@[simp] theorem readByte_writeWord (m : Mem) (a x : W) (v : W) :
    (m.writeWord a v).readByte x =
      if x = a + 3 then v.extractLsb' 24 8 else if x = a + 2 then v.extractLsb' 16 8
      else if x = a + 1 then v.extractLsb' 8 8 else if x = a then v.extractLsb' 0 8
      else m.readByte x := by
  simp only [Mem.writeWord, readByte_writeByte]

@[simp] theorem readByte_writeHalf (m : Mem) (a x : W) (v : BitVec 16) :
    (m.writeHalf a v).readByte x =
      if x = a + 1 then v.extractLsb' 8 8 else if x = a then v.extractLsb' 0 8
      else m.readByte x := by
  simp only [Mem.writeHalf, readByte_writeByte]

/-- The four little-endian bytes of a word reassemble to the word. -/
theorem append_wordBytes (w : W) :
    w.extractLsb' 24 8 ++ w.extractLsb' 16 8 ++ w.extractLsb' 8 8 ++ w.extractLsb' 0 8 = w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h8 : i < 8
  · simp [h8]
  by_cases h16 : i < 16
  · simp [h8, show i - 8 < 8 by omega, show 8 + (i - 8) = i by omega]
  by_cases h24 : i < 24
  · simp [h8, show ¬ i - 8 < 8 by omega, show i - 8 - 8 < 8 by omega,
      show 16 + (i - 8 - 8) = i by omega]
  · simp [h8, show ¬ i - 8 < 8 by omega, show ¬ i - 8 - 8 < 8 by omega,
      show i - 8 - 8 - 8 < 8 by omega, show 24 + (i - 8 - 8 - 8) = i by omega]

theorem readWord_of_bytes (m : Mem) (a w : W)
    (h0 : m.readByte a = w.extractLsb' 0 8) (h1 : m.readByte (a + 1) = w.extractLsb' 8 8)
    (h2 : m.readByte (a + 2) = w.extractLsb' 16 8) (h3 : m.readByte (a + 3) = w.extractLsb' 24 8) :
    m.readWord a = w := by
  rw [readWord_eq, h0, h1, h2, h3, append_wordBytes]

end Flapjack.Mips32.TargetProof
