import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.StoreEach
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.HeapExpand
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteStore
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.StateLaws

/-! Recovering the constructor's free word region from the actual heap relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- Writing a separated free region establishes the exact word-list assertion
for the values written, while preserving the entire disjoint frame. -/
theorem storeEachMemory_wordList {width : Nat} [NeZero width]
    (base offset : BitVec width) (values : List (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (free : SetSep.star (Misc.wordListExists (base + offset) values.length) frame
      (SetSep.fun2Set (memory, fun addr => domain addr = true))) :
    SetSep.star (Misc.wordList (base + offset) values) frame
      (SetSep.fun2Set (storeEachMemory base offset values memory, fun addr => domain addr = true)) := by
  classical
  induction values generalizing offset memory frame with
  | nil =>
    simpa [storeEachMemory, Misc.wordList,
      (StackRemove.WordListExists.wordListExistsThm (β := WordLocW width) (base + offset) 0).1] using free
  | cons value values ih =>
    simp only [List.length_cons, (StackRemove.WordListExists.wordListExistsThm (base + offset) values.length).2] at free
    obtain ⟨region, outer, split, ⟨old, head, tail, inner, singleton, rest⟩, outerInv⟩ := free
    have exposed : SetSep.star (SetSep.one (base + offset, old))
        (SetSep.star (Misc.wordListExists (base + offset + StackRemove.bytesInWord width) values.length) frame)
        (SetSep.fun2Set (memory, fun addr => domain addr = true)) := by
      rw [SetSep.starAssoc]
      exact ⟨region, outer, split, ⟨head, tail, inner, singleton, rest⟩, outerInv⟩
    have written := SetSep.writeFun2Set value (base + offset) old _ memory (fun addr => domain addr = true) exposed
    rw [SetSep.starComm, star_swap_first] at written
    have tailFree : SetSep.star
        (Misc.wordListExists (base + (offset + BitVec.ofNat width (width / 8))) values.length)
        (SetSep.star (SetSep.one (base + offset, value)) frame)
        (SetSep.fun2Set ((fun key => if key = base + offset then value else memory key),
          fun addr => domain addr = true)) := by
      simp only [StackRemove.bytesInWord, BitVec.add_assoc] at written
      convert written using 1
      congr 2
      funext key
      by_cases same : key = base + offset <;> simp [same]
    have tailResult := ih (offset + BitVec.ofNat width (width / 8)) _ _ tailFree
    rw [star_swap_first, SetSep.starAssoc] at tailResult
    simpa [storeEachMemory, Misc.wordList, StackRemove.bytesInWord, BitVec.add_assoc] using tailResult

/-- The heap/store relation exposes the requested prefix of the free region
at the actual next-free address, retaining both other heap regions as a frame.
This is Flapjack simulation infrastructure. -/
theorem heapInMemoryStore_constructorFree {width : Nat} [NeZero width]
    (conf : Config) (pre post : ValueHeap width) (sp sp1 count : Nat) (gens : GcCombined.GenState)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width)) (memory : BitVec width → WordLocW width)
    (domain : BitVec width → Bool) (limit : Nat) (enough : count ≤ sp + sp1)
    (heapMem : heapInMemoryStore (pre ++ heapExpand (sp + sp1) ++ post)
      (heapLength pre) sp sp1 gens conf store memory domain limit) :
    ∃ curr, store.lookup .currHeap = some (.word curr) ∧
      store.lookup .nextFree = some (.word (curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre))) ∧
      ∃ frame, SetSep.star
        (Misc.wordListExists (curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre)) count)
        frame (SetSep.fun2Set (memory, fun addr => domain addr = true)) := by
  obtain ⟨_, _, _, _, _, _, _, curr, other, _, _, currStore, _, nextStore, _, _, _, _, _, separated⟩ := heapMem
  refine ⟨curr, currStore, nextStore, ?_⟩
  rw [List.append_assoc, wordHeapAppend, wordHeapAppend, wordHeap_heapExpand] at separated
  have sum : sp + sp1 = count + ((sp + sp1) - count) := by omega
  rw [sum, StackRemove.Proofs.WordListMemory.wordListExistsAdd] at separated
  rw [← SetSep.starAssoc, ← SetSep.starAssoc] at separated
  rw [star_swap_first] at separated
  rw [← SetSep.starAssoc] at separated
  exact ⟨_, separated⟩

/-- Once the generated setup has loaded `nextFree` into the base register,
the actual heap/store relation justifies every constructor-field store. -/
theorem evaluate_storeEach_from_heap {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (pre post : ValueHeap width) (sp sp1 : Nat) (gens : GcCombined.GenState)
    (baseName : Nat) (names : List Nat) (values : List (WordLocW width))
    (state : WordSemStateFiniteExact width C F) (limit : Nat)
    (enough : names.length ≤ sp + sp1)
    (heapMem : heapInMemoryStore (pre ++ heapExpand (sp + sp1) ++ post)
      (heapLength pre) sp sp1 gens conf state.store state.memory state.mdomain limit)
    (baseRun : WordSemStateFiniteExact.getVar baseName state = state.store.lookup .nextFree)
    (valuesRun : WordSemStateFiniteExact.getVars names state = some values) :
    ∃ base, WordSemStateFiniteExact.getVar baseName state = some (.word base) ∧
      WordSemStateFiniteExact.evaluate (storeEach baseName names 0) state =
        (none, { state with memory := storeEachMemory base 0 values state.memory }) := by
  obtain ⟨curr, _, nextStore, frame, free⟩ := heapInMemoryStore_constructorFree conf pre post sp sp1 names.length gens
    state.store state.memory state.mdomain limit enough heapMem
  let base := curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre)
  have baseValue : WordSemStateFiniteExact.getVar baseName state = some (.word base) := by
    simpa [base] using baseRun.trans nextStore
  refine ⟨base, baseValue, ?_⟩
  apply evaluate_storeEach_of_freeRegion baseName names 0 base values state baseValue valuesRun frame
  simpa [base] using free

/-- The generated stores both execute and turn the corresponding free-region
assertion into the exact written word list, preserving the surrounding frame. -/
theorem evaluate_storeEach_layout_from_heap {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (pre post : ValueHeap width) (sp sp1 : Nat) (gens : GcCombined.GenState)
    (baseName : Nat) (names : List Nat) (values : List (WordLocW width))
    (state : WordSemStateFiniteExact width C F) (limit : Nat)
    (enough : names.length ≤ sp + sp1)
    (heapMem : heapInMemoryStore (pre ++ heapExpand (sp + sp1) ++ post)
      (heapLength pre) sp sp1 gens conf state.store state.memory state.mdomain limit)
    (baseRun : WordSemStateFiniteExact.getVar baseName state = state.store.lookup .nextFree)
    (valuesRun : WordSemStateFiniteExact.getVars names state = some values) :
    ∃ base frame, WordSemStateFiniteExact.getVar baseName state = some (.word base) ∧
      WordSemStateFiniteExact.evaluate (storeEach baseName names 0) state =
        (none, { state with memory := storeEachMemory base 0 values state.memory }) ∧
      SetSep.star (Misc.wordList base values) frame
        (SetSep.fun2Set (storeEachMemory base 0 values state.memory, fun addr => state.mdomain addr = true)) := by
  obtain ⟨curr, _, nextStore, frame, free⟩ := heapInMemoryStore_constructorFree conf pre post sp sp1 names.length gens
    state.store state.memory state.mdomain limit enough heapMem
  let base := curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre)
  have baseValue : WordSemStateFiniteExact.getVar baseName state = some (.word base) := by
    simpa [base] using baseRun.trans nextStore
  have sameLength := WordSemStateFiniteExact.getVarsLengthLemma names state values valuesRun
  have free' : SetSep.star (Misc.wordListExists (base + 0) values.length) frame
      (SetSep.fun2Set (state.memory, fun addr => state.mdomain addr = true)) := by
    simpa [base, sameLength] using free
  refine ⟨base, frame, baseValue, ?_, ?_⟩
  · apply evaluate_storeEach_of_freeRegion baseName names 0 base values state baseValue valuesRun frame
    simpa [sameLength] using free'
  · simpa using storeEachMemory_wordList base 0 values state.memory state.mdomain frame free'

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
