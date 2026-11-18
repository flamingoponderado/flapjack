module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.StoreList

@[expose] public section

/-! Writing into a separated free word region. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- A sufficiently long separated free region supports the complete list
store and leaves the unused suffix and arbitrary frame intact. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "IMP_store_list_SOME"
  (words_as_type_indexed_bitvec)]
theorem storeList_exists {width : Nat} [NeZero width]
    (words : List (WordLocW width)) (address : BitVec width) (count : Nat)
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (other : ((BitVec width × WordLocW width) → Prop) → Prop)
    (premises : SetSep.star (Misc.wordListExists address count) other
        (SetSep.fun2Set (memory, fun a => domain a = true)) ∧ words.length ≤ count) :
    ∃ memory1, storeList address words memory domain = some memory1 ∧
      SetSep.star (SetSep.star (Misc.wordList address words)
        (Misc.wordListExists (address + StackRemove.bytesInWord width * BitVec.ofNat width words.length)
          (count - words.length))) other (SetSep.fun2Set (memory1, fun a => domain a = true)) := by
  classical
  induction words generalizing address count memory other with
  | nil =>
    refine ⟨memory, rfl, ?_⟩
    simpa [Misc.wordList, StackRemove.StackHeap.starEmptyLeft] using premises.1
  | cons word words ih =>
    obtain ⟨separated, bound⟩ := premises
    cases count with
    | zero => simp at bound
    | succ count =>
      have tailBound : words.length ≤ count := by simpa using bound
      rw [(StackRemove.WordListExists.wordListExistsThm (β := WordLocW width) address count).2] at separated
      obtain ⟨left, right, partition, ⟨old, headTail⟩, frame⟩ := separated
      have oneSep : SetSep.star (SetSep.one (address, old))
          (SetSep.star (Misc.wordListExists (address + StackRemove.bytesInWord width) count) other)
          (SetSep.fun2Set (memory, fun a => domain a = true)) := by
        rw [SetSep.starAssoc]
        exact ⟨left, right, partition, headTail, frame⟩
      have inDomain : domain address = true := by
        obtain ⟨oneHeap, frameHeap, split, oneProof, _⟩ := oneSep
        have member : SetSep.fun2Set (memory, fun a => domain a = true) (address, old) := by
          rw [← split.1]
          left
          rw [oneProof]
        exact ((SetSep.fun2SetThm memory (fun a => domain a = true) address old).mp member).2
      let memory' := fun key => if key = address then word else memory key
      have changed := SetSep.writeFun2Set word address old _ memory (fun a => domain a = true) oneSep
      rw [← SetSep.starAssoc, SetSep.starComm other (SetSep.one (address, word))] at changed
      have memoryEq : (fun key => @ite (WordLocW width) (key = address)
          (Classical.propDecidable _) word (memory key)) = memory' := by
        funext key
        by_cases h : key = address <;> simp [memory', h]
      rw [memoryEq] at changed
      obtain ⟨memory1, stored, final⟩ := ih (address + StackRemove.bytesInWord width) count memory'
        (SetSep.star (SetSep.one (address, word)) other) ⟨changed, tailBound⟩
      refine ⟨memory1, ?_, ?_⟩
      · simpa [storeList, inDomain, memory', wordSemBytesInWord, StackRemove.bytesInWord] using stored
      · simp only [Misc.wordList, List.length_cons]
        have addressEq : address + StackRemove.bytesInWord width +
            StackRemove.bytesInWord width * BitVec.ofNat width words.length =
            address + StackRemove.bytesInWord width * BitVec.ofNat width (words.length + 1) := by
          simp [BitVec.ofNat_add, BitVec.mul_add, BitVec.add_assoc, BitVec.add_comm]
        simp only [← SetSep.starAssoc] at final ⊢
        rw [star_swap_first (Misc.wordListExists _ _) (SetSep.one (address, word)) other] at final
        rw [star_swap_first (Misc.wordList _ _) (SetSep.one (address, word)) _] at final
        simpa [addressEq] using final

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
