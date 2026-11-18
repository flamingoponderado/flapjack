module

public import Flapjack.Compiler.Backend.Semantics.WordSem.Alloc
public import Flapjack.Pancake.Semantics.PanSem.DecCallExact

@[expose] public section

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

@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "IMP_loc_merge_APPEND"
  (words_as_type_indexed_bitvec)]
theorem locMerge_append_of_length {width : Nat} [NeZero width] (ts qs xs ys : List (WordLocW width))
    (h : (ts.filter wordSemIsWordLoc).length = qs.length) :
    locMerge (ts ++ xs) (qs ++ ys) = locMerge ts qs ++ locMerge xs ys := by
  induction ts generalizing qs with
  | nil =>
    cases qs <;> simp_all [locMerge]
  | cons t ts ih =>
    cases t with
    | loc a b =>
      simp only [List.filter_cons, wordSemIsWordLoc, Bool.false_eq_true, ↓reduceIte] at h
      simp only [List.cons_append, locMerge]
      rw [ih qs h]
    | word w =>
      cases qs with
      | nil => simp [wordSemIsWordLoc] at h
      | cons q qs =>
        simp only [List.filter_cons, wordSemIsWordLoc, ↓reduceIte, List.length_cons, Nat.succ.injEq] at h
        simp only [List.cons_append, locMerge]
        rw [ih qs h]

@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "TAKE_DROP_loc_merge_APPEND"
  (words_as_type_indexed_bitvec)]
theorem take_drop_locMerge_append {width : Nat} [NeZero width] {β : Type} (q : List (β × WordLocW width))
    (xs ys : List (WordLocW width)) :
    ((locMerge (q.map Prod.snd) xs ++ ys).take q.length = locMerge (q.map Prod.snd) xs) ∧
    ((locMerge (q.map Prod.snd) xs ++ ys).drop q.length = ys) := by
  have h : (locMerge (q.map Prod.snd) xs).length = q.length := by simp [length_locMerge]
  rw [← h]
  simp

@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "loc_merge_NIL"
  (words_as_type_indexed_bitvec)]
theorem locMerge_nil {width : Nat} [NeZero width] (xs : List (WordLocW width)) : locMerge xs [] = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [locMerge, ih]

@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "loc_merge_APPEND"
  (words_as_type_indexed_bitvec)]
theorem locMerge_append_split {width : Nat} [NeZero width] (xs1 xs2 ys : List (WordLocW width)) :
    ∃ zs1 zs2, locMerge (xs1 ++ xs2) ys = zs1 ++ zs2 ∧
      zs1.length = xs1.length ∧ xs2.length = xs2.length ∧ ∃ ts, locMerge xs2 ts = zs2 := by
  induction xs1 generalizing ys with
  | nil => exact ⟨[], locMerge xs2 ys, rfl, rfl, rfl, ys, rfl⟩
  | cons x xs1 ih =>
    cases x with
    | loc a b =>
      obtain ⟨zs1, zs2, eq, len, taut, ts, tail⟩ := ih ys
      refine ⟨.loc a b :: zs1, zs2, ?_, ?_, taut, ts, tail⟩
      · simpa [locMerge] using congrArg (List.cons (.loc a b)) eq
      · simp [len]
    | word w =>
      cases ys with
      | nil =>
        refine ⟨.word w :: xs1, xs2, ?_, rfl, rfl, [], locMerge_nil xs2⟩
        simp [locMerge]
      | cons y ys =>
        obtain ⟨zs1, zs2, eq, len, taut, ts, tail⟩ := ih ys
        refine ⟨y :: zs1, zs2, ?_, ?_, taut, ts, tail⟩
        · simpa [locMerge] using congrArg (List.cons y) eq
        · simp [len]

@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "EVERY2_loc_merge"
  (words_as_type_indexed_bitvec)]
theorem every2_locMerge {width : Nat} [NeZero width] (xs ys : List (WordLocW width)) :
    ListRel (fun x y => (wordSemIsWordLoc y = true → wordSemIsWordLoc x = true) ∧
      (wordSemIsWordLoc x = false → x = y)) xs (locMerge xs ys) := by
  have reflRel : ∀ zs : List (WordLocW width), ListRel (fun x y => (wordSemIsWordLoc y = true → wordSemIsWordLoc x = true) ∧ (wordSemIsWordLoc x = false → x = y)) zs zs := by
    intro zs
    induction zs with
    | nil => exact .nil
    | cons z zs ih => exact .cons ⟨fun h => h, fun _ => rfl⟩ ih
  induction xs generalizing ys with
  | nil => exact .nil
  | cons x xs ih =>
    cases x with
    | loc a b =>
      simp only [locMerge]
      exact .cons ⟨by simp [wordSemIsWordLoc], fun _ => rfl⟩ (ih ys)
    | word w =>
      cases ys with
      | nil =>
        rw [locMerge_nil]
        exact .cons ⟨fun _ => rfl, by simp [wordSemIsWordLoc]⟩ (reflRel xs)
      | cons y ys =>
        simp only [locMerge]
        exact .cons ⟨fun _ => rfl, by simp [wordSemIsWordLoc]⟩ (ih ys)

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
