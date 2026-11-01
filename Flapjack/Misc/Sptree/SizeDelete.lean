import Flapjack.Misc.Sptree

/-! Size of sparse trees after deleting an occupied key. -/
namespace Flapjack

private theorem size_mkBN {α : Type} (left right : Spt α) :
    sptSize (sptMkBN left right) = sptSize left + sptSize right := by
  cases left <;> cases right <;> simp [sptMkBN, sptSize]

private theorem size_mkBS {α : Type} (left : Spt α) (value : α) (right : Spt α) :
    sptSize (sptMkBS left value right) = sptSize left + sptSize right + 1 := by
  cases left <;> cases right <;> simp [sptMkBS, sptSize]

/-- Flapjack termination helper: deleting an occupied key decreases size.
HOL `size_delete` states the more general exact size for every key. -/
theorem sptSize_delete_lt {α : Type} (tree : Spt α) (key : Nat)
    (present : sptLookup key tree ≠ none) : sptSize (sptDelete key tree) < sptSize tree := by
  induction tree generalizing key with
  | ln => simp [sptLookup] at present
  | ls value =>
    by_cases zero : key = 0
    · simp [sptDelete, zero, sptSize]
    · simp [sptLookup, zero] at present
  | bn left right ihLeft ihRight =>
    by_cases zero : key = 0
    · simp [sptLookup, zero] at present
    · by_cases even : key % 2 = 0
      · have existsLeft : sptLookup ((key - 1) / 2) left ≠ none := by simpa [sptLookup, zero, even] using present
        have smaller := ihLeft _ existsLeft
        simp [sptDelete, zero, even, size_mkBN, sptSize]
        omega
      · have existsRight : sptLookup ((key - 1) / 2) right ≠ none := by simpa [sptLookup, zero, even] using present
        have smaller := ihRight _ existsRight
        simp [sptDelete, zero, even, size_mkBN, sptSize]
        omega
  | bs left value right ihLeft ihRight =>
    by_cases zero : key = 0
    · simp [sptDelete, zero, sptSize]
    · by_cases even : key % 2 = 0
      · have existsLeft : sptLookup ((key - 1) / 2) left ≠ none := by simpa [sptLookup, zero, even] using present
        have smaller := ihLeft _ existsLeft
        simp [sptDelete, zero, even, size_mkBS, sptSize]
        omega
      · have existsRight : sptLookup ((key - 1) / 2) right ≠ none := by simpa [sptLookup, zero, even] using present
        have smaller := ihRight _ existsRight
        simp [sptDelete, zero, even, size_mkBS, sptSize]
        omega

end Flapjack
