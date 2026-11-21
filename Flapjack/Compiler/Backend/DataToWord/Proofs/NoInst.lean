module

public import Flapjack.Compiler.Backend.DataToWord.Control
public import Flapjack.Pancake.WordConvs

@[expose] public section

/-! Instruction conventions of straight-line data-to-word code
(`data_to_wordProofScript.sml` lines 2271-2366). -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Encoders.Asm

/-- `everyInst` of a `wordListSeq` is the conjunction over its parts.
Flapjack-specific helper; HOL unfolds `list_Seq_def` inline. -/
theorem everyInst_wordListSeq {width : Nat} [NeZero width]
    (P : WordLangInst (BitVec width) → Bool) :
    ∀ xs : List (WordLangProgHOL (BitVec width)),
      everyInst P (wordListSeq xs) = xs.all (everyInst P)
  | [] => by simp [wordListSeq, everyInst]
  | [x] => by simp [wordListSeq]
  | x :: y :: xs => by
    rw [wordListSeq, everyInst, everyInst_wordListSeq P (y :: xs)]
    simp

@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "StoreEach_no_inst"
  (words_as_type_indexed_bitvec)]
theorem storeEach_noInst {width : Nat} [NeZero width] (ac : AsmConfigExact width) :
    ∀ (a : Nat) (ls : List Nat) (off : BitVec width),
      everyInst (fun i => instOkLessExact ac (HolInst.ofWordLangInst i)) (storeEach a ls off) = true
  | _, [], _ => by simp [storeEach, everyInst]
  | a, _ :: ls, off => by
    simp [storeEach, everyInst, storeEach_noInst ac a ls]

@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "MemEqList_no_inst"
  (words_as_type_indexed_bitvec)]
theorem memEqList_noInst {width : Nat} [NeZero width] (ac : AsmConfigExact width) :
    ∀ (a : BitVec width) (x : List (BitVec width)),
      everyInst (fun i => instOkLessExact ac (HolInst.ofWordLangInst i)) (memEqList a x) = true
  | _, [] => by simp [memEqList, everyInst]
  | a, _ :: x => by
    simp [memEqList, everyInst, memEqList_noInst ac _ x]

@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "StoreAnyConsts_no_inst"
  (words_as_type_indexed_bitvec)]
theorem storeAnyConsts_noInst {width : Nat} [NeZero width] (ac : AsmConfigExact width)
    (r1 r2 r3 : Nat) (ws : List (Bool × WordLocW width)) (w : Bool × WordLocW width) :
    everyInst (fun i => instOkLessExact ac (HolInst.ofWordLangInst i))
      (storeAnyConsts r1 r2 r3 ws w) = true := by
  induction ws using storeAnyConsts.induct with
  | case1 =>
    unfold storeAnyConsts
    rcases w with ⟨b, v⟩
    cases v <;> simp [everyInst]
  | case2 _ block _ rest ih =>
    unfold storeAnyConsts
    rw [everyInst_wordListSeq]
    simp [everyInst, ih]
  | case3 b word rest _ ih =>
    unfold storeAnyConsts
    simpa [everyInst] using ih

/-- HOL's word `≤` is the signed comparison `word_le`, rendered by
`BitVec.sle`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "bounds_lem"
  (words_as_type_indexed_bitvec)]
theorem bounds_lem {width : Nat} [NeZero width] (w : BitVec width)
    (h : (width = 32 ∨ width = 64) ∧
      (w = -3 ∨ w = -2 ∨ w = -1 ∨ w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 4 ∨ w = 5 ∨
        w = 6 ∨ w = 7)) :
    (-8 : BitVec width).sle w = true ∧ w.sle 8 = true := by
  rcases h with ⟨hw | hw, hv⟩ <;> subst width <;>
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end Flapjack.Compiler.Backend.DataToWord.Proofs
