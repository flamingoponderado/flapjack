module
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.StoreList
public import Flapjack.Compiler.Backend.StackRemove.Proofs.WordListExists
@[expose] public section
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend

/-- Storing into an existential word list preserves the arbitrary separated frame. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "store_list_thm"
  (words_as_type_indexed_bitvec)]
theorem storeListThm {width : Nat} [NeZero width] (xs : List (WordLocW width))
    (a : BitVec width) (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (m : BitVec width → WordLocW width) (dm : BitVec width → Bool)
    (h : SetSep.star (Misc.wordListExists a xs.length) frame
      (SetSep.fun2Set (m, fun x => dm x = true))) :
    ∃ m1, storeList a xs m dm = some m1 ∧
      SetSep.star (Misc.wordList a xs) frame (SetSep.fun2Set (m1, fun x => dm x = true)) := by
  induction xs generalizing a frame m with
  | nil =>
    refine ⟨m, by simp [storeList], ?_⟩
    simp only [List.length_nil] at h
    rw [(StackRemove.WordListExists.wordListExistsThm (β := WordLocW width) a 0).1] at h
    simpa [Misc.wordList] using h
  | cons x xs ih =>
    have ex := (StackRemove.WordListExists.wordListExistsThm (β := WordLocW width) a xs.length).2
    simp only [List.length_cons, ex, SetSep.star, SetSep.sepExists] at h
    obtain ⟨left, right, partition, ⟨old, head, tail, split, single, tailInv⟩, frameInv⟩ := h
    have grouped : SetSep.star (SetSep.one (a, old))
        (SetSep.star (Misc.wordListExists (a + StackRemove.bytesInWord width) xs.length) frame)
        (SetSep.fun2Set (m, fun x => dm x = true)) := by
      rw [SetSep.starAssoc]
      exact ⟨left, right, partition, ⟨head, tail, split, single, tailInv⟩, frameInv⟩
    have domain : dm a = true := by
      obtain ⟨head, rest, split, one, _⟩ := grouped
      have inHead : head (a, old) := by rw [one]
      have graph : SetSep.fun2Set (m, fun x => dm x = true) (a, old) := by
        rw [← split.1]; exact Or.inl inHead
      exact ((SetSep.fun2SetThm m (fun x => dm x = true) a old).mp graph).2
    have wrote := SetSep.writeFun2Set x a old
      (SetSep.star (Misc.wordListExists (a + StackRemove.bytesInWord width) xs.length) frame)
      m (fun x => dm x = true) grouped
    have tailFrame : SetSep.star (Misc.wordListExists (a + StackRemove.bytesInWord width) xs.length)
        (SetSep.star (SetSep.one (a, x)) frame)
        (SetSep.fun2Set ((fun key => if key = a then x else m key), fun x => dm x = true)) := by
      rw [SetSep.starComm (SetSep.one (a, x)) frame, SetSep.starAssoc]
      convert wrote using 4
      rename_i key
      by_cases same : key = a <;> simp [same]
    obtain ⟨m1, run, post⟩ := ih _ _ _ tailFrame
    refine ⟨m1, ?_, ?_⟩
    · simp only [storeList, domain, ↓reduceIte]
      simpa [wordSemBytesInWord, StackRemove.bytesInWord] using run
    · change SetSep.star (SetSep.star (SetSep.one (a, x))
        (Misc.wordList (a + StackRemove.bytesInWord width) xs)) frame _
      rw [SetSep.starAssoc, SetSep.starComm (Misc.wordList (a + StackRemove.bytesInWord width) xs) (SetSep.one (a, x))] at post
      exact post
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
