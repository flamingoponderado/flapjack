module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteStore

@[expose] public section

/-! Byte-array cell writes inside separated heaps. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord Flapjack.HolByte

/-- Flapjack infrastructure for the HOL byte heap update: preserve the
header, validity conditions, and frame while writing a packed byte. -/
theorem wordEl_byteStore {width : Nat} [NeZero width] (conf : Config) (bytes : List (BitVec 8)) (words : List (BitVec width))
    (be flag : Bool) (j r : Nat) (byte : BitVec 8) (good : goodDimindex width)
    (rbound : r < width / 8) (ibound : j * (width / 8) + r < bytes.length)
    (jbound : j < words.length) (base : BitVec width)
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Prop)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (separated : SetSep.star (wordEl base (bytesRep be flag bytes words) conf) frame
      (SetSep.fun2Set (memory, domain))) :
    let packed := writeBytes bytes words be
    let oldWord := packed[j]'(by dsimp [packed]; simpa [writeBytes_wordCount] using jbound)
    let addr := base + StackRemove.bytesInWord width + BitVec.ofNat width j * StackRemove.bytesInWord width
    memory addr = .word oldWord ∧ domain addr ∧
    SetSep.star (wordEl base (bytesRep be flag (bytes.set (j * (width / 8) + r) byte) words) conf) frame
      (SetSep.fun2Set ((fun key => if key = addr then .word (setByte (BitVec.ofNat width r) byte oldWord be)
        else memory key), domain)) := by
  simp only [wordEl, bytesRep, wordPayload, List.isEmpty_nil, Bool.true_and, List.length_map,
    Misc.wordList, ← SetSep.starAssoc] at separated
  rw [star_swap_first] at separated
  have changed := wordList_packedByteWrite bytes words be j r byte good rbound ibound jbound
    (base + StackRemove.bytesInWord width) memory domain _ separated
  dsimp only at changed ⊢
  obtain ⟨read, inDomain, result⟩ := changed
  refine ⟨read, inDomain, ?_⟩
  rw [star_swap_first] at result
  simpa [wordEl, bytesRep, wordPayload, List.length_map, List.length_set, writeBytes_wordCount, Misc.wordList, ← SetSep.starAssoc] using result

/-- Lift the framed byte-cell write through an arbitrary heap prefix and
suffix. This is a step toward the original heap-in-memory update theorem. -/
theorem wordHeap_byteStore {width : Nat} [NeZero width] (conf : Config) (bytes : List (BitVec 8)) (words : List (BitVec width))
    (be flag : Bool) (j r : Nat) (byte : BitVec 8) (good : goodDimindex width)
    (rbound : r < width / 8) (ibound : j * (width / 8) + r < bytes.length)
    (jbound : j < words.length) (curr : BitVec width) (pre post : ValueHeap width)
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Prop)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (separated : SetSep.star (wordHeap curr (pre ++ [bytesRep be flag bytes words] ++ post) conf) frame
      (SetSep.fun2Set (memory, domain))) :
    let packed := writeBytes bytes words be
    let oldWord := packed[j]'(by dsimp [packed]; simpa [writeBytes_wordCount] using jbound)
    let base := curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre)
    let addr := base + StackRemove.bytesInWord width + BitVec.ofNat width j * StackRemove.bytesInWord width
    memory addr = .word oldWord ∧ domain addr ∧
    SetSep.star (wordHeap curr (pre ++ [bytesRep be flag (bytes.set (j * (width / 8) + r) byte) words] ++ post) conf) frame
      (SetSep.fun2Set ((fun key => if key = addr then .word (setByte (BitVec.ofNat width r) byte oldWord be)
        else memory key), domain)) := by
  rw [List.append_assoc, wordHeapAppend] at separated
  simp only [List.singleton_append, wordHeap, ← SetSep.starAssoc] at separated
  rw [star_swap_first] at separated
  have changed := wordEl_byteStore conf bytes words be flag j r byte good rbound ibound jbound
    (curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre)) memory domain _ separated
  dsimp only at changed ⊢
  obtain ⟨read, inDomain, result⟩ := changed
  refine ⟨read, inDomain, ?_⟩
  rw [star_swap_first] at result
  rw [List.append_assoc, wordHeapAppend]
  simp only [List.singleton_append, wordHeap, ← SetSep.starAssoc]
  simpa [bytesRep, elLength, writeBytes_wordCount] using result

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
