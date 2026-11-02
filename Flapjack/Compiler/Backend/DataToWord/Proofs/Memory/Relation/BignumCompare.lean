import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.NumberHeader
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.WordCompare
import Flapjack.Misc.Multiword.Length

/-! Signed comparison of the concrete multiword bignum payloads. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Misc.Multiword
open Classical
noncomputable section

/-- Comparing equal-length magnitude lists in sign-adjusted order yields the
    original integer comparison code. This is Flapjack infrastructure for the
    source memory-relation comparison theorem. -/
theorem bignumMagnitudeCompare {width : Nat} [NeZero width] (i1 i2 : Int)
    (sameSign : (i1 < 0 ↔ i2 < 0))
    (sameLength : (n2mw i1.natAbs : List (BitVec width)).length =
      (n2mw i2.natAbs : List (BitVec width)).length) :
    (match mwCmp (if i1 < 0 then n2mw (width := width) i2.natAbs else n2mw i1.natAbs)
        (if i1 < 0 then n2mw (width := width) i1.natAbs else n2mw i2.natAbs) with
      | none => (1 : BitVec width) | some true => 0 | some false => 2) = wordCmpRes i1 i2 := by
  by_cases negative : i1 < 0
  · have negative2 : i2 < 0 := sameSign.mp negative
    simp only [negative, ↓reduceIte]
    rw [mwCmpThm _ _ sameLength, mw2n_n2mw, mw2n_n2mw]
    cases i1 <;> cases i2 <;> simp_all [wordCmpRes]
    all_goals repeat' first | split | contradiction
    all_goals simp_all <;> omega
  · have nonnegative2 : ¬ i2 < 0 := fun h => negative (sameSign.mpr h)
    simp only [negative, ↓reduceIte]
    rw [mwCmpThm _ _ sameLength.symm, mw2n_n2mw, mw2n_n2mw]
    cases i1 <;> cases i2 <;> simp_all [wordCmpRes]
    all_goals repeat' first | split | contradiction
    all_goals simp_all

/-- The target comparison loop returns the signed integer comparison code
    when both separated magnitude payloads have equal length and sign. -/
theorem bignumWordLoop {width : Nat} [NeZero width] (i1 i2 : Int)
    (frame1 frame2 : ((BitVec width × WordLocW width) → Prop) → Prop)
    (a1 a2 : BitVec width) (domain : BitVec width → Bool) (memory : BitVec width → WordLocW width)
    (sameSign : (i1 < 0 ↔ i2 < 0))
    (sameLength : (n2mw i1.natAbs : List (BitVec width)).length =
      (n2mw i2.natAbs : List (BitVec width)).length)
    (bound : (n2mw i1.natAbs : List (BitVec width)).length < 2 ^ width)
    (first : SetSep.star (Misc.wordList (a1 + StackRemove.bytesInWord width)
      ((n2mw i1.natAbs : List (BitVec width)).map WordLocW.word)) frame1
      (SetSep.fun2Set (memory, fun a => domain a = true)))
    (second : SetSep.star (Misc.wordList (a2 + StackRemove.bytesInWord width)
      ((n2mw i2.natAbs : List (BitVec width)).map WordLocW.word)) frame2
      (SetSep.fun2Set (memory, fun a => domain a = true))) :
    let count := BitVec.ofNat width (n2mw i1.natAbs : List (BitVec width)).length
    let start1 := a1 + StackRemove.bytesInWord width * count
    let start2 := a2 + StackRemove.bytesInWord width * count
    wordCmpLoop count (if i1 < 0 then start2 else start1) (if i1 < 0 then start1 else start2)
      domain memory = some (wordCmpRes i1 i2) := by
  have correct := bignumMagnitudeCompare (width := width) i1 i2 sameSign sameLength
  by_cases negative : i1 < 0
  · simp only [negative, ↓reduceIte] at correct ⊢
    have bound2 : (n2mw i2.natAbs : List (BitVec width)).length < 2 ^ width := by rw [← sameLength]; exact bound
    have loop := wordCmpLoopThm (n2mw i2.natAbs) (n2mw i1.natAbs) frame2 frame1 a2 a1 domain memory
      ⟨sameLength.symm, bound2, second, first⟩
    rw [← sameLength] at loop
    cases outcome : mwCmp (n2mw (width := width) i2.natAbs) (n2mw i1.natAbs) with
    | none => simpa [outcome] using loop.trans (congrArg some correct)
    | some flag => cases flag <;> simpa [outcome] using loop.trans (congrArg some correct)
  · simp only [negative, ↓reduceIte] at correct ⊢
    have loop := wordCmpLoopThm (n2mw i1.natAbs) (n2mw i2.natAbs) frame1 frame2 a1 a2 domain memory
      ⟨sameLength, bound, first, second⟩
    cases outcome : mwCmp (n2mw (width := width) i1.natAbs) (n2mw i2.natAbs) with
    | none => simpa [outcome] using loop.trans (congrArg some correct)
    | some flag => cases flag <;> simpa [outcome] using loop.trans (congrArg some correct)

end
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
