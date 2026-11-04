import Flapjack.Compiler.Backend.Semantics.WordSem.Alloc

/-! Reconstructing stack roots after collection. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- Replace word roots in order, retaining code locations and any suffix
for which the collector supplied no replacement. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "loc_merge_def"
  (words_as_type_indexed_bitvec)]
def locMerge {width : Nat} [NeZero width] :
    List (WordLocW width) → List (WordLocW width) → List (WordLocW width)
  | [], _ => []
  | .loc a b :: xs, ys => .loc a b :: locMerge xs ys
  | .word w :: xs, [] => .word w :: xs
  | .word _ :: xs, y :: ys => y :: locMerge xs ys

@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "LENGTH_loc_merge"
  (words_as_type_indexed_bitvec)]
theorem length_locMerge {width : Nat} [NeZero width] (xs ys : List (WordLocW width)) :
    (locMerge xs ys).length = xs.length := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih =>
    cases x with
    | loc a b => simp [locMerge, ih]
    | word w => cases ys <;> simp [locMerge, ih]

@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "loc_merge_FILTER_isWord"
  (words_as_type_indexed_bitvec)]
theorem locMerge_filter_isWord {width : Nat} [NeZero width] (xs : List (WordLocW width)) :
    locMerge xs (xs.filter wordSemIsWordLoc) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases x <;> simp only [List.filter_cons, wordSemIsWordLoc, Bool.false_eq_true, ↓reduceIte, locMerge, ih]

/-- Any root list with the encoded stack's length can refill the original
frame layout. This Lean-side length lemma is used to prove the source result. -/
theorem decStack_of_length {width : Nat} [NeZero width]
    (stack : List (WordSemStackFrame width)) (roots : List (WordLocW width))
    (lengths : roots.length = (wordSemEncStack stack).length) :
    ∃ stack', wordSemDecStack roots stack = some stack' := by
  induction stack generalizing roots with
  | nil =>
    cases roots with
    | nil => exact ⟨[], rfl⟩
    | cons root roots => simp [wordSemEncStack] at lengths
  | cons frame stack ih =>
    cases frame with
    | stackFrame size nonGc gc handler =>
      have len : roots.length = gc.length + (wordSemEncStack stack).length := by
        simpa [wordSemEncStack] using lengths
      have enough : ¬ roots.length < gc.length := by omega
      have tailLength : (roots.drop gc.length).length = (wordSemEncStack stack).length := by
        simp only [List.length_drop]
        omega
      obtain ⟨rest, decoded⟩ := ih (roots.drop gc.length) tailLength
      refine ⟨.stackFrame size nonGc ((gc.map Prod.fst).zip (roots.take gc.length)) handler :: rest, ?_⟩
      simp [wordSemDecStack, enough, decoded]

@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "dec_stack_loc_merge_enc_stack"
  (words_as_type_indexed_bitvec)]
theorem decStack_locMerge_encStack {width : Nat} [NeZero width]
    (stack : List (WordSemStackFrame width)) (roots : List (WordLocW width)) :
    ∃ stack', wordSemDecStack (locMerge (wordSemEncStack stack) roots) stack = some stack' := by
  apply decStack_of_length
  exact length_locMerge _ _

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
