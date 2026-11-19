module

public import Flapjack.Byte.BytesToWord
public import Mathlib.Tactic
@[expose] public section

/-! Equality of bounded byte-to-word conversions. -/
namespace Flapjack.HolByte
/-- Inputs agreeing throughout the requested prefix yield the same word.
The bounds provide the proofs required by Lean’s indexed list notation. -/
@[hol "HOL/src/n-bit/byteScript.sml" "bytes_to_word_same"
  (words_as_type_indexed_bitvec)]
theorem bytesToWord_same {width : Nat} [NeZero width] (count : Nat) (address : BitVec width)
    (first : List (BitVec 8)) (word : BitVec width) (be : Bool) (second : List (BitVec 8))
    (h : ∀ n, n < count → ∃ (h1 : n < first.length) (h2 : n < second.length), first[n] = second[n]) :
    bytesToWord count address first word be = bytesToWord count address second word be := by
  induction count generalizing address first second with
  | zero => rfl
  | succ count ih =>
    have h0 := h 0 (by omega)
    obtain ⟨bound1, bound2, firstEq⟩ := h0
    cases first with
    | nil => simp at bound1
    | cons x xs =>
      cases second with
      | nil => simp at bound2
      | cons y ys =>
        have eq : x = y := by simpa using firstEq
        subst y
        simp only [bytesToWord]
        congr 1
        apply ih
        intro n hn
        have hnext := h (n + 1) (by omega)
        obtain ⟨bound1, bound2, eq⟩ := hnext
        exact ⟨by simpa using bound1, by simpa using bound2, by simpa using eq⟩

end Flapjack.HolByte
