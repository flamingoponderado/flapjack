module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteUpdate
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BytePackingUpdate
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockElement
public import Flapjack.Compiler.Backend.LabToTarget.InstMem
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Heap
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteUpdateStack

@[expose] public section

/-! Concrete writes to a separated packed byte payload. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord Flapjack.HolByte

/-- Exchange the first two separated assertions while retaining the frame. -/
theorem star_swap_first {α : Type} (p q r : (α → Prop) → Prop) :
    SetSep.star p (SetSep.star q r) = SetSep.star q (SetSep.star p r) := by
  rw [SetSep.starAssoc, SetSep.starComm p q, ← SetSep.starAssoc]

/-- Writing one element of a separated word list updates exactly its graph
entry and preserves the entire external separation frame. -/
theorem wordList_write {width : Nat} [NeZero width] {β : Type}
    (address : BitVec width) (values : List β) (i : Nat) (newValue : β)
    (memory : BitVec width → β) (domain : BitVec width → Prop)
    (frame : ((BitVec width × β) → Prop) → Prop) (bound : i < values.length)
    (separated : SetSep.star (Misc.wordList address values) frame (SetSep.fun2Set (memory, domain))) :
    SetSep.star (Misc.wordList address (values.set i newValue)) frame
      (SetSep.fun2Set ((fun key => if key = address + BitVec.ofNat width i * StackRemove.bytesInWord width
        then newValue else memory key), domain)) := by
  classical
  induction values generalizing address i frame with
  | nil => simp at bound
  | cons value values ih =>
    cases i with
    | zero =>
      simp only [List.set_cons_zero, Misc.wordList, ← SetSep.starAssoc] at separated ⊢
      have changed := SetSep.writeFun2Set newValue address value _ memory domain separated
      rw [SetSep.starComm] at changed
      convert changed using 2
      congr 1
      funext key
      by_cases h : key = address <;> simp [h]
    | succ i =>
      simp only [List.set_cons_succ, Misc.wordList, ← SetSep.starAssoc] at separated ⊢
      rw [star_swap_first] at separated
      have changed := ih (address + StackRemove.bytesInWord width) i
        (SetSep.star (SetSep.one (address, value)) frame) (by simpa using bound) separated
      rw [star_swap_first] at changed
      have addressEq : (address + StackRemove.bytesInWord width) +
          BitVec.ofNat width i * StackRemove.bytesInWord width =
          address + BitVec.ofNat width (i + 1) * StackRemove.bytesInWord width := by
        simp only [BitVec.ofNat_add, BitVec.add_mul, BitVec.one_mul]
        ac_rfl
      simpa only [addressEq] using changed

/-- Flapjack separation infrastructure for the original
`heap_in_memory_store_UpdateByte` proof: a packed byte update reads and writes
its containing word while preserving an arbitrary disjoint frame. -/
theorem wordList_packedByteWrite {width : Nat} [NeZero width] (bytes : List (BitVec 8)) (words : List (BitVec width))
    (be : Bool) (j r : Nat) (byte : BitVec 8) (good : goodDimindex width)
    (rbound : r < width / 8) (ibound : j * (width / 8) + r < bytes.length)
    (jbound : j < words.length) (address : BitVec width)
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Prop)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (separated : SetSep.star (Misc.wordList address ((writeBytes bytes words be).map WordLocW.word)) frame
      (SetSep.fun2Set (memory, domain))) :
    let packed := writeBytes bytes words be
    let newValue := WordLocW.word (setByte (BitVec.ofNat width r) byte (packed[j]'(by dsimp [packed]; simpa [writeBytes_wordCount] using jbound)) be)
    memory (address + BitVec.ofNat width j * StackRemove.bytesInWord width) =
      .word (packed[j]'(by dsimp [packed]; simpa [writeBytes_wordCount] using jbound)) ∧
    domain (address + BitVec.ofNat width j * StackRemove.bytesInWord width) ∧
    SetSep.star (Misc.wordList address ((writeBytes (bytes.set (j * (width / 8) + r) byte) words be).map WordLocW.word)) frame
      (SetSep.fun2Set ((fun key => if key = address + BitVec.ofNat width j * StackRemove.bytesInWord width
        then newValue else memory key), domain)) := by
  dsimp only
  have bound : j < (writeBytes bytes words be).length := by simpa [writeBytes_wordCount] using jbound
  have packedEq := writeBytes_setByte bytes words be j r byte good rbound ibound
  have mappedEq : (writeBytes (bytes.set (j * (width / 8) + r) byte) words be).map WordLocW.word =
      ((writeBytes bytes words be).map WordLocW.word).set j
        (.word (setByte (BitVec.ofNat width r) byte ((writeBytes bytes words be)[j]) be)) := by
    rw [packedEq, List.modify_eq_set, List.map_set]
    simp [bound]
  have inGraph : SetSep.fun2Set (memory, domain)
      (address + BitVec.ofNat width j * StackRemove.bytesInWord width,
        .word ((writeBytes bytes words be)[j])) := by
    obtain ⟨payload, rest, split, wordsAssertion, _⟩ := separated
    rw [← split.1]
    left
    have member := wordList_indexMember ((writeBytes bytes words be).map WordLocW.word) j
      (by simpa using bound) address payload wordsAssertion
    simpa using member
  obtain ⟨memoryEq, inDomain⟩ := (SetSep.fun2SetThm memory domain _ _).mp inGraph
  refine ⟨memoryEq, inDomain, ?_⟩
  rw [mappedEq]
  exact wordList_write address _ j _ memory domain frame (by simpa using bound) separated

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
