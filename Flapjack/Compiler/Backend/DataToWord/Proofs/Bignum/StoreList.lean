module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.StoreList

@[expose] public section

/-! Sequential stores over a separated word list in the bignum proof. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum
open Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- A separated singleton cell is mapped in the domain to its value. -/
private theorem one_star_fun2Set {width : Nat} [NeZero width]
    {address : BitVec width} {value : WordLocW width}
    {rest : ((BitVec width × WordLocW width) → Prop) → Prop}
    {memory : BitVec width → WordLocW width} {domain : BitVec width → Bool}
    (sep : SetSep.star (SetSep.one (address, value)) rest
      (SetSep.fun2Set (memory, fun a => domain a = true))) :
    memory address = value ∧ domain address = true := by
  obtain ⟨oneHeap, _, split, oneProof, _⟩ := sep
  have member : SetSep.fun2Set (memory, fun a => domain a = true) (address, value) := by
    rw [← split.1]
    left
    rw [oneProof]
  exact (SetSep.fun2SetThm memory (fun a => domain a = true) address value).mp member

/-- Storing back the words already described by a separated word list leaves
memory unchanged. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml" "word_list_IMP_store_list"
  (words_as_type_indexed_bitvec)]
theorem wordList_imp_storeList {width : Nat} [NeZero width] :
    ∀ (xs : List (WordLocW width)) (a : BitVec width)
      (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
      (m : BitVec width → WordLocW width) (dm : BitVec width → Bool),
      SetSep.star (Misc.wordList a xs) frame (SetSep.fun2Set (m, fun x => dm x = true)) →
      storeList a xs m dm = some m := by
  intro xs
  induction xs with
  | nil => intro a frame m dm _; rfl
  | cons h xs ih =>
    intro a frame m dm sep
    simp only [Misc.wordList] at sep
    rw [← SetSep.starAssoc] at sep
    obtain ⟨value, inDomain⟩ := one_star_fun2Set sep
    have same : (fun key => if key = a then h else m key) = m := by
      funext key
      by_cases eq : key = a
      · subst eq; simp [value]
      · simp [eq]
    have tail : SetSep.star (Misc.wordList (a + StackRemove.bytesInWord width) xs)
        (SetSep.star frame (SetSep.one (a, h)))
        (SetSep.fun2Set (m, fun x => dm x = true)) := by
      have s := sep
      rw [SetSep.starComm (SetSep.one _) _, ← SetSep.starAssoc] at s
      exact s
    have stored := ih (a + StackRemove.bytesInWord width) _ m dm tail
    simp only [storeList, inDomain, if_true, same]
    simpa [wordSemBytesInWord, StackRemove.bytesInWord] using stored

/-- A separated word list can be overwritten with zero words, preserving the
frame. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml" "word_list_store_list"
  (words_as_type_indexed_bitvec)]
theorem wordList_storeList {width : Nat} [NeZero width] :
    ∀ (xs : List (WordLocW width)) (a : BitVec width)
      (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
      (m : BitVec width → WordLocW width) (dm : BitVec width → Bool),
      SetSep.star (Misc.wordList a xs) frame (SetSep.fun2Set (m, fun x => dm x = true)) →
      ∃ m2, storeList a (List.replicate xs.length (WordLocW.word (0 : BitVec width))) m dm = some m2 ∧
        SetSep.star (Misc.wordList a (List.replicate xs.length (WordLocW.word (0 : BitVec width)))) frame
          (SetSep.fun2Set (m2, fun x => dm x = true)) := by
  classical
  let zeroWord : WordLocW width := .word 0
  intro xs
  induction xs with
  | nil => intro a frame m dm sep; exact ⟨m, rfl, sep⟩
  | cons h xs ih =>
    intro a frame m dm sep
    simp only [Misc.wordList] at sep
    rw [← SetSep.starAssoc] at sep
    obtain ⟨_, inDomain⟩ := one_star_fun2Set sep
    let m' := fun key => if key = a then zeroWord else m key
    have changed := SetSep.writeFun2Set zeroWord a h _ m (fun x => dm x = true) sep
    have memoryEq : (fun key => @ite (WordLocW width) (key = a)
        (Classical.propDecidable _) zeroWord (m key)) = m' := by
      funext key
      by_cases eq : key = a <;> simp [m', eq]
    rw [memoryEq] at changed
    have tail : SetSep.star (Misc.wordList (a + StackRemove.bytesInWord width) xs)
        (SetSep.star frame (SetSep.one (a, zeroWord)))
        (SetSep.fun2Set (m', fun x => dm x = true)) := by
      rw [← SetSep.starAssoc] at changed
      exact changed
    obtain ⟨m2, stored, final⟩ := ih (a + StackRemove.bytesInWord width) _ m' dm tail
    refine ⟨m2, ?_, ?_⟩
    · simp only [List.length_cons, List.replicate_succ, storeList, inDomain, if_true]
      simpa [m', zeroWord, wordSemBytesInWord, StackRemove.bytesInWord] using stored
    · simp only [List.length_cons, List.replicate_succ, Misc.wordList]
      rw [SetSep.starComm frame (SetSep.one _), SetSep.starAssoc,
        SetSep.starComm (Misc.wordList _ _) (SetSep.one _)] at final
      exact final

end Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum
