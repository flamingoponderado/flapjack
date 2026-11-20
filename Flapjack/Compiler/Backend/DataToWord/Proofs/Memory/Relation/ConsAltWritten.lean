module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ConsMemory
public import Flapjack.Misc.SetSep.Top
@[expose] public section

/-! Constructor allocation after its words have already been stored. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend

/-- Storing the words already asserted by a separated word list leaves memory unchanged.
This is proof infrastructure for constructor allocation, with no separate HOL declaration. -/
private theorem storeList_same {width : Nat} [NeZero width]
    (address : BitVec width) (words : List (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (separated : SetSep.star (Misc.wordList address words) frame
      (SetSep.fun2Set (memory, fun k => domain k = true))) :
    storeList address words memory domain = some memory := by
  classical
  induction words generalizing address frame with
  | nil => rfl
  | cons word words ih =>
    have member : SetSep.fun2Set (memory, fun k => domain k = true) (address, word) := by
      obtain ⟨left, right, split, listMem, _⟩ := separated
      rw [← split.1]
      left
      have h := wordList_indexMember (word :: words) 0 (by simp) address left listMem
      simp only [BitVec.zero_mul, BitVec.add_zero] at h
      change left (address, word) at h
      exact h
    obtain ⟨read, live⟩ := (SetSep.fun2SetThm memory (fun k => domain k = true) address word).mp member
    have tail : SetSep.star (Misc.wordList (address + StackRemove.bytesInWord width) words)
        (SetSep.star (SetSep.one (address, word)) frame)
        (SetSep.fun2Set (memory, fun k => domain k = true)) := by
      simp only [Misc.wordList, ← SetSep.starAssoc] at separated
      rwa [star_swap_first] at separated
    have update : (fun key => if key = address then word else memory key) = memory := by
      funext key
      by_cases eq : key = address <;> simp [eq, read]
    simp only [storeList, live, ↓reduceIte, update]
    simpa [wordSemBytesInWord, StackRemove.bytesInWord] using ih (address + StackRemove.bytesInWord width)
      (SetSep.star (SetSep.one (address, word)) frame) tail


/-- The constructor relation after the complete word list has been written. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_Cons_alt"
  (fmap_as_finite_support_relation := [st]) (words_as_type_indexed_bitvec)
  (cons_alt_existential_inhabitants := [β._unused])]
theorem memoryRel_consAlt {width : Nat} [NeZero width] {β : Type} [Nonempty β]
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (be : Bool) (ts : Nat)
    (refs : Spt (Flapjack.Compiler.Backend.BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (sp : Nat) (st : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (vals : List Flapjack.Compiler.Backend.DataSem.Value) (ws : List (WordLocW width))
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) (tag : Nat) (hd : BitVec width)
    (rel : memoryRel conf be ts refs sp st memory domain (vals.zip ws ++ vars))
    (lens : vals.length = ws.length) (nonempty : vals ≠ [])
    (encoded : Flapjack.Compiler.Backend.DataToWord.encodeHeader conf (4 * tag) ws.length = some hd)
    (enough : ws.length < sp) (good : goodDimindex width) :
    ∃ (free curr : BitVec width) (_unused : β),
      st.lookup .nextFree = some (.word free) ∧ st.lookup .currHeap = some (.word curr) ∧
      (SetSep.star (Misc.wordList free (.word hd :: ws)) SetSep.sepT
        (SetSep.fun2Set (memory, fun key => domain key = true)) →
        memoryRel conf be (ts + 1) refs (sp - (ws.length + 1))
          (st.update (.nextFree, .word (free + wordSemBytesInWord * BitVec.ofNat width (ws.length + 1)))) memory domain
          ((.block ts tag vals, Flapjack.Compiler.Backend.DataToWord.Build.makeConsPtr conf (free - curr) tag ws.length) :: vars)) := by
  obtain ⟨free, curr, written, freeRead, currRead, run, result⟩ :=
    memoryRel_cons1 conf be ts refs sp st memory domain vals ws vars tag hd rel lens nonempty encoded enough good
  refine ⟨free, curr, Classical.choice inferInstance, freeRead, currRead, ?_⟩
  intro separated
  have same := storeList_same free (.word hd :: ws) memory domain SetSep.sepT separated
  rw [same] at run
  have : written = memory := Option.some.inj run.symm
  simpa [this] using result

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
