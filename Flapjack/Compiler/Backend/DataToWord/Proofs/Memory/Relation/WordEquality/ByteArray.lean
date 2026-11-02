import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BytePacking
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.WordCompare

/-! Comparison of packed byte-array payloads. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Misc.Multiword
open Classical
noncomputable section

/-- Packing preserves the number of payload words. -/
private theorem packedLength {width : Nat} [NeZero width] (be : Bool)
    (words : List (BitVec width)) (bytes : List (BitVec 8)) :
    (DataToWord.writeBytes bytes words be).length = words.length := by
  induction words generalizing bytes with
  | nil => rfl
  | cons x xs ih => simp [DataToWord.writeBytes, ih]

/-- Comparing two separated packed payloads returns one exactly when their
    byte sequences agree. This is Flapjack infrastructure for the original
    reference-equality simulation. -/
theorem byteArrayWordEqualityLoop {width : Nat} [NeZero width] (be : Bool)
    (words : List (BitVec width)) (bytes1 bytes2 : List (BitVec 8))
    (frame1 frame2 : ((BitVec width × WordLocW width) → Prop) → Prop)
    (a1 a2 : BitVec width) (domain : BitVec width → Bool) (memory : BitVec width → WordLocW width)
    (good : goodDimindex width) (sameLength : bytes1.length = bytes2.length)
    (capacity : bytes1.length ≤ words.length * (width / 8))
    (wordCount : words.length ≤ bytes1.length / (width / 8) + 1)
    (bound : words.length < 2 ^ width)
    (first : SetSep.star (Misc.wordList (a1 + StackRemove.bytesInWord width)
      ((DataToWord.writeBytes bytes1 words be).map WordLocW.word)) frame1
      (SetSep.fun2Set (memory, fun a => domain a = true)))
    (second : SetSep.star (Misc.wordList (a2 + StackRemove.bytesInWord width)
      ((DataToWord.writeBytes bytes2 words be).map WordLocW.word)) frame2
      (SetSep.fun2Set (memory, fun a => domain a = true))) :
    ∃ result : BitVec width,
      wordCmpLoop (BitVec.ofNat width words.length)
        (a1 + StackRemove.bytesInWord width * BitVec.ofNat width words.length)
        (a2 + StackRemove.bytesInWord width * BitVec.ofNat width words.length) domain memory = some result ∧
      (bytes1 = bytes2 ↔ result = 1) := by
  let xs := DataToWord.writeBytes bytes1 words be
  let ys := DataToWord.writeBytes bytes2 words be
  have xsLength : xs.length = words.length := packedLength be words bytes1
  have ysLength : ys.length = words.length := packedLength be words bytes2
  have lengths : xs.length = ys.length := xsLength.trans ysLength.symm
  have packed : (xs = ys ↔ bytes1 = bytes2) := writeBytesInj be good words bytes1 bytes2 ⟨sameLength, capacity, wordCount⟩
  have magnitude : (mw2n xs = mw2n ys ↔ bytes1 = bytes2) := (mw2nInj xs ys lengths).trans packed
  have loop := wordCmpLoopThm xs ys frame1 frame2 a1 a2 domain memory
    ⟨lengths, by simpa [xsLength] using bound, first, second⟩
  have cmp := mwCmpThm xs ys lengths.symm
  by_cases equal : bytes1 = bytes2
  · have same := magnitude.mpr equal
    have result : mwCmp xs ys = none := by simpa [same] using cmp
    refine ⟨1, ?_, by simp [equal]⟩
    simpa [xsLength, result] using loop
  · have different : mw2n xs ≠ mw2n ys := fun h => equal (magnitude.mp h)
    by_cases less : mw2n xs < mw2n ys
    · have result : mwCmp xs ys = some true := by simpa [different, less] using cmp
      refine ⟨0, ?_, ?_⟩
      · simpa [xsLength, result] using loop
      · rcases good with h | h <;> subst width <;> simp [equal]
    · have result : mwCmp xs ys = some false := by simpa [different, less] using cmp
      refine ⟨2, ?_, ?_⟩
      · simpa [xsLength, result] using loop
      · rcases good with h | h <;> subst width <;> simp [equal]

end
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
