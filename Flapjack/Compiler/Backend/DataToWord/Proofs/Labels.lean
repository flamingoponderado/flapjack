module

public import Flapjack.Compiler.Backend.DataToWord.Control
public import Flapjack.Pancake.WordConvs

@[expose] public section

/-! Label facts for the straight-line word code emitted by data-to-word
compilation (`data_to_wordProofScript.sml` lines 1921-2046). -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack Flapjack.Compiler.Backend.DataToWord

/-- `extractLabels` of a `wordListSeq` is the concatenation of the labels of
its parts. Flapjack-specific helper; HOL unfolds `list_Seq_def` inline. -/
theorem extractLabels_wordListSeq {width : Nat} [NeZero width] :
    ∀ xs : List (WordLangProgHOL (BitVec width)),
      extractLabels (wordListSeq xs) = (xs.map extractLabels).flatten
  | [] => by simp [wordListSeq, extractLabels]
  | [x] => by simp [wordListSeq]
  | x :: y :: xs => by
    rw [wordListSeq, extractLabels, extractLabels_wordListSeq (y :: xs)]
    simp

@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "extract_labels_MemEqList"
  (words_as_type_indexed_bitvec)]
theorem extractLabels_memEqList {width : Nat} [NeZero width] :
    ∀ (a : BitVec width) (x : List (BitVec width)), extractLabels (memEqList a x) = []
  | _, [] => by simp [memEqList, extractLabels]
  | a, _ :: ws => by
    simp [memEqList, extractLabels, extractLabels_memEqList _ ws]

@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "extract_labels_StoreEach"
  (words_as_type_indexed_bitvec)]
theorem extractLabels_storeEach {width : Nat} [NeZero width] :
    ∀ (xs : List Nat) (a : Nat) (d : BitVec width), extractLabels (storeEach a xs d) = []
  | [], _, _ => by simp [storeEach, extractLabels]
  | _ :: xs, a, d => by
    simp [storeEach, extractLabels, extractLabels_storeEach xs]

@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "extract_labels_StoreAnyConsts"
  (words_as_type_indexed_bitvec)]
theorem extractLabels_storeAnyConsts {width : Nat} [NeZero width] (r1 r2 r3 : Nat)
    (ws : List (Bool × WordLocW width)) (w : Bool × WordLocW width) :
    extractLabels (storeAnyConsts r1 r2 r3 ws w : WordLangProgHOL (BitVec width)) = [] := by
  induction ws using storeAnyConsts.induct with
  | case1 =>
    unfold storeAnyConsts
    rcases w with ⟨b, v⟩
    cases v <;> simp [extractLabels]
  | case2 _ block _ rest ih =>
    unfold storeAnyConsts
    simp [extractLabels_wordListSeq, extractLabels, ih]
  | case3 b word rest _ ih =>
    unfold storeAnyConsts
    simpa [extractLabels] using ih

@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "extract_labels_WordOp64_on_32"
  (words_as_type_indexed_bitvec)]
theorem extractLabels_wordOp64On32 {width : Nat} [NeZero width] (f : BackendCommon.Opw) :
    extractLabels (wordOp64On32 f : WordLangProgHOL (BitVec width)) = [] := by
  cases f <;> simp [wordOp64On32, extractLabels_wordListSeq, extractLabels]

@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "extract_labels_WordShift64_on_32"
  (words_as_type_indexed_bitvec)]
theorem extractLabels_wordShift64On32 {width : Nat} [NeZero width] (f : Shift) (g : Nat) :
    extractLabels (wordShift64On32 f g : WordLangProgHOL (BitVec width)) = [] := by
  unfold wordShift64On32
  rw [extractLabels_wordListSeq]
  cases f <;> by_cases h : g % 64 < 32 <;> by_cases h2 : g < 32 <;> simp [h, h2, extractLabels]

@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "labels_rel_emp"]
theorem labelsRel_emp {α : Type} (ls : List α) (h : labelsRel ([] : List α) ls) : ls = [] := by
  cases ls with
  | nil => rfl
  | cons x _ => exact absurd (h.2 x (by simp)) (by simp)

end Flapjack.Compiler.Backend.DataToWord.Proofs
