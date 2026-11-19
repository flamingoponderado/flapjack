module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteUpdateRefs
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BytePacking
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataSem Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.DataToWord.Proofs.Memory


@[expose] public section
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- A byte heap element occupies one header word plus its zero buffer. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "el_length_Bytes"
  (words_as_type_indexed_bitvec)]
theorem elLengthBytes {width : Nat} [NeZero width] (be flag : Bool) (vals : List (BitVec 8)) (zeros : List (BitVec width)) :
    elLength (bytesRep be flag vals zeros) = zeros.length + 1 := by
  simp [bytesRep, elLength, writeBytes_wordCount]

/-- Updating the second byte-array reference preserves block uniqueness for both references. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "blocks_unique_insert_ByteArray2"]
theorem blocksUniqueInsertByteArray2 {α : Type} (ts : Nat) (refs : Spt (BvlSem.Ref Value)) (bl1 bl2 : Bool) (p1 p2 : Nat)
    (vars : List (Value × α)) (flag : Bool) (res : List (BitVec 8))
    (unique : blocksUnique ts (allValues refs (.refPtr bl1 p1 :: .refPtr bl2 p2 :: vars.map Prod.fst))) :
    blocksUnique ts (allValues (sptInsert p2 (.byteArray flag res) refs)
      (.refPtr bl1 p1 :: .refPtr bl2 p2 :: vars.map Prod.fst)) := by
  intro stamp tag1 xs1 tag2 xs2 h
  exact unique stamp tag1 xs1 tag2 xs2
    ⟨allValues_insertByteArray_subset refs _ p2 flag res _ h.1, h.2.1,
      allValues_insertByteArray_subset refs _ p2 flag res _ h.2.2.1, h.2.2.2⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
