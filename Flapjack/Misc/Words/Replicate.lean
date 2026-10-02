import Flapjack.Misc.Alignment

/-! Counterpart of the pinned wordsScript word-replication group. -/
namespace Flapjack

/-- HOL's complete bitwise repetition equation. Independent positive dimensions
retain both truncation and zero filling beyond the requested repetitions.
Modulo the positive input dimension keeps every raw HOL FCP index in range. -/
@[hol "HOL/src/n-bit/wordsScript.sml" "word_replicate_def" (words_as_type_indexed_bitvec)]
def holWordReplicate (outputWidth : Nat) [NeZero outputWidth]
    {inputWidth : Nat} [NeZero inputWidth] (n : Nat) (w : BitVec inputWidth) :
    BitVec outputWidth :=
  holFcpWord (fun i => decide (i < n * inputWidth) && w.getLsbD (i % inputWidth))

/-- Flapjack bit-observation infrastructure for the literal FCP equation. -/
theorem getLsbD_holWordReplicate (outputWidth : Nat) [NeZero outputWidth]
    {inputWidth : Nat} [NeZero inputWidth] (n : Nat) (w : BitVec inputWidth) (i : Nat) :
    (holWordReplicate outputWidth n w).getLsbD i =
      (decide (i < outputWidth) &&
        (decide (i < n * inputWidth) && w.getLsbD (i % inputWidth))) := by
  exact getLsbD_holFcpWord _ i

end Flapjack
