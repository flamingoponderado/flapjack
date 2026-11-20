module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteConcrete
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteXorInvariants
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.DataToWord.Proofs.Memory


@[expose] public section
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- Expose a byte cell's packed payload while retaining its header, surrounding heap and external frame. This Flapjack-specific separation identity supports the original `memory_rel_xor_bytes` proof, which performs the same decomposition inline. -/
theorem byteHeapFrame {width : Nat} [NeZero width] (c : Config) (curr : BitVec width)
    (pre post : ValueHeap width) (bytes : List (BitVec 8)) (be flag : Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (good : goodDimindex width) (config : c.lenSize + 7 < width)
    (countBound : bytes.length / (width / 8) + 1 < 2 ^ (width - 4))
    (lenBound : bytes.length / (width / 8) + 1 < 2 ^ c.lenSize) :
    let words := List.replicate (bytes.length / (width / 8) + 1) (0 : BitVec width)
    let headerAddr := curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre)
    let postAddr := headerAddr + StackRemove.bytesInWord width * BitVec.ofNat width (words.length + 1)
    SetSep.star (wordHeap curr (pre ++ [bytesRep be flag bytes words] ++ post) c) frame =
      SetSep.star (Misc.wordList (headerAddr + StackRemove.bytesInWord width) ((writeBytes bytes words be).map WordLocW.word))
        (SetSep.star (SetSep.star (wordHeap curr pre c) (SetSep.one (headerAddr, .word (makeByteHeader c flag bytes.length))))
          (SetSep.star (wordHeap postAddr post c) frame)) := by
  dsimp only
  rw [List.append_assoc, wordHeapAppend]
  simp only [List.singleton_append, wordHeap, elLengthBytes, List.length_replicate]
  rw [wordElBytesEq c _ bytes be flag good config countBound lenBound]
  simp only [Misc.wordList]
  let : Std.Associative (@SetSep.star (BitVec width × WordLocW width)) := ⟨fun a b c => (SetSep.starAssoc a b c).symm⟩
  let : Std.Commutative (@SetSep.star (BitVec width × WordLocW width)) := ⟨fun a b => SetSep.starComm a b⟩
  ac_rfl

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
