module

public import Flapjack.Compiler.Backend.DataToWord.Control
public import Flapjack.Pancake.WordConvs.NotCreated

@[expose] public section

/-! Absence of `ShareInst` in straight-line data-to-word code
(`data_to_wordProofScript.sml` lines 2075-2180). -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack Flapjack.Compiler.Backend.DataToWord

@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "list_Seq_no_share_inst"
  (words_as_type_indexed_bitvec)]
theorem listSeq_noShareInst {width : Nat} [NeZero width] :
    ∀ xs : List (WordLangProgHOL (BitVec width)),
      noShareInstSubprogsHOL (wordListSeq xs) = xs.all noShareInstSubprogsHOL
  | [] => by simp [wordListSeq, noShareInstSubprogsHOL, notCreatedSubprogsWithMemOp]
  | [x] => by simp [wordListSeq]
  | x :: y :: xs => by
    have ih := listSeq_noShareInst (y :: xs)
    rw [wordListSeq]
    simp only [noShareInstSubprogsHOL, notCreatedSubprogsWithMemOp] at ih ⊢
    rw [ih]
    simp [noShareInstSubprogsHOL]

@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "StoreEach_no_share_inst"
  (words_as_type_indexed_bitvec)]
theorem storeEach_noShareInst {width : Nat} [NeZero width] :
    ∀ (v : Nat) (xs : List Nat) (offset : BitVec width),
      noShareInstSubprogsHOL (storeEach v xs offset) = true
  | _, [], _ => by simp [storeEach, noShareInstSubprogsHOL, notCreatedSubprogsWithMemOp]
  | v, _ :: xs, offset => by
    have ih := storeEach_noShareInst v xs (offset + (wordSemBytesInWord : BitVec width))
    simp only [noShareInstSubprogsHOL] at ih ⊢
    simp [storeEach, notCreatedSubprogsWithMemOp, ih]

@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "MemEqList_no_share_inst"
  (words_as_type_indexed_bitvec)]
theorem memEqList_noShareInst {width : Nat} [NeZero width] :
    ∀ (a : BitVec width) (xs : List (BitVec width)),
      noShareInstSubprogsHOL (memEqList a xs) = true
  | _, [] => by simp [memEqList, noShareInstSubprogsHOL, notCreatedSubprogsWithMemOp]
  | a, _ :: xs => by
    have ih := memEqList_noShareInst (a + (wordSemBytesInWord : BitVec width)) xs
    simp only [noShareInstSubprogsHOL] at ih ⊢
    simp [memEqList, notCreatedSubprogsWithMemOp, ih]

@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "StoreAnyConsts_no_share_inst"
  (words_as_type_indexed_bitvec)]
theorem storeAnyConsts_noShareInst {width : Nat} [NeZero width] (r1 r2 r3 : Nat)
    (vs : List (Bool × WordLocW width)) (v : Bool × WordLocW width) :
    noShareInstSubprogsHOL (storeAnyConsts r1 r2 r3 vs v : WordLangProgHOL (BitVec width)) = true := by
  induction vs using storeAnyConsts.induct with
  | case1 =>
    unfold storeAnyConsts
    rcases v with ⟨b, w⟩
    cases w <;> simp [noShareInstSubprogsHOL, notCreatedSubprogsWithMemOp]
  | case2 _ block _ rest ih =>
    unfold storeAnyConsts
    rw [listSeq_noShareInst]
    simp only [List.all_cons, List.all_nil, Bool.and_true, ih]
    simp [noShareInstSubprogsHOL, notCreatedSubprogsWithMemOp]
  | case3 b word rest _ ih =>
    unfold storeAnyConsts
    simp only [noShareInstSubprogsHOL] at ih ⊢
    simpa [notCreatedSubprogsWithMemOp] using ih

@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "MAP_FST_ZIP"]
theorem map_fst_zip {α β : Type} (xs : List α) (ys : List β) :
    (xs.zip ys).map Prod.fst = xs.take ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih => cases ys <;> simp [ih]

end Flapjack.Compiler.Backend.DataToWord.Proofs
