import Flapjack.Compiler.Backend.WordToStack.LiveBitmap
import Flapjack.Compiler.Backend.WordToStack.Proofs.BitmapBitStructure
import Flapjack.Compiler.Backend.WordToStack.Proofs.ListUpdate
import Flapjack.Compiler.Backend.Semantics.WordSem.State

namespace Flapjack.Compiler.Backend.WordToStack
open Flapjack

/-- Flapjack structural support: the appended true sentinel occupies an
in-range bit. This helper has no independently named HOL declaration. -/
private theorem sentinelNotZero {width : Nat} [NeZero width]
    (bits : List Bool) (h : bits.length < width) :
    (bitsToWordW (bits ++ [true]) : BitVec width) ≠ 0 := by
  intro hz
  have hb := BitmapBitStructureSupport.bitmapBitLookup (width := width)
    (bits ++ [true]) bits.length h
  simp [hz] at hb

/-- Flapjack structural support: both terminal and continuation chunks carry
a nonzero sentinel. No stack shape or bitmap contents are assumed. -/
private theorem sentinelWordListHead {width : Nat} [NeZero width]
    (bits : List Bool) (hwidth : 8 ≤ width) :
    ∃ (word : BitVec width) (words : List (BitVec width)),
      wordListW (bits ++ [true]) (width - 1) = word :: words ∧ word ≠ 0 := by
  rw [wordListW]
  split
  · rename_i h
    refine ⟨_, [], rfl, sentinelNotZero bits ?_⟩
    simp only [List.length_append, List.length_cons, List.length_nil] at h
    omega
  · refine ⟨_, _, rfl, sentinelNotZero _ ?_⟩
    have ht := List.length_take_le (width - 1) (bits ++ [true])
    omega

/-- Full original bitmap overwrite exclusion, including empty and truncated
destination lists. Only the original dimension-at-least-eight guard remains. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "list_LUPDATE_write_bitmap_NOT_NIL" (words_as_type_indexed_bitvec)]
theorem listUpdateWriteBitmapNotNil {width : Nat} [NeZero width] {α : Type}
    (names : Spt α) (k frame : Nat) (xs : List (WordLocW width))
    (hwidth : 8 ≤ width) :
    listUpdate ((writeBitmapExact names k frame).map WordLocW.word) 0 xs ≠
      [WordLocW.word (0 : BitVec width)] := by
  obtain ⟨word, words, hw, hn⟩ := sentinelWordListHead (width := width)
    ((List.range frame).map (fun x => decide
      (x ∈ (sptToAList names).map
        (fun (entry : Nat × α) => frame - 1 - (entry.1 / 2 - k))))) hwidth
  have hb : writeBitmapExact (width := width) names k frame = word :: words := hw
  rw [hb, List.map_cons]
  cases xs with
  | nil => simp [listUpdateNil]
  | cons x xs =>
    rw [listUpdateZeroCons]
    intro he
    have hew : word = 0 := by simpa using (List.cons.inj he).1
    exact hn hew

/-- Literal original DROP_list_LUPDATE specialization at equal offsets;
the source derives it from the unconditional reflexive offset bound. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "DROP_list_LUPDATE_lemma"]
theorem dropListUpdateSameOffset {α : Type} (ys : List α) (n : Nat) (xs : List α) :
    (listUpdate ys n xs).drop n = listUpdate ys 0 (xs.drop n) := by
  simpa using dropListUpdate ys n n xs (Nat.le_refl n)

/-- Full original frame-prefix decomposition. The third size is retained
in the original guard, although the conclusion only selects the second size. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "APPEND_LEMMA"]
theorem appendFrameLemma {α : Type} (n1 n2 n3 : Nat) (xs : List α)
    (h : n1 + n2 + n3 ≤ xs.length) :
    ∃ xs2 xs3, xs.drop n1 = xs2 ++ xs3 ∧ n2 = xs2.length := by
  refine ⟨(xs.drop n1).take n2, (xs.drop n1).drop n2, ?_, ?_⟩
  · exact (List.take_append_drop n2 (xs.drop n1)).symm
  · simp only [List.length_take, List.length_drop]
    omega

end Flapjack.Compiler.Backend.WordToStack
