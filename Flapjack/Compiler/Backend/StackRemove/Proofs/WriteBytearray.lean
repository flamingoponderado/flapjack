import Flapjack.Compiler.Backend.Semantics.WordSem
import Flapjack.Pancake.Semantics.LoopSem

/- Declaration-local alignment review (user correction, 2026-10-02): the
original three proofs use byte_align only as a common aligned-address key.
They unfold tail-first read/write/load/store clauses and functional updates;
none evaluates LOG2 or assumes a numerical alignment law. These are portable
original-shaped numerical instances with unchanged executable operators, at
all positive widths. No equality with HOL's unspecified LOG2 0, runtime rewrite,
out-of-domain default policy, or cross-prover equivalence is asserted. -/

namespace Flapjack.Compiler.Backend.StackRemove
open Flapjack

/-- Flapjack factoring of the actual byte-store clauses: a successful store
changes only its aligned address. There is no separate HOL declaration here. -/
private theorem storeOther {width : Nat} [NeZero width]
    (memory result : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (bigEndian : Bool) (address point : BitVec width) (byte : BitVec 8)
    (different : point ≠ riscvByteAlignHOL address)
    (stored : memStoreByteAuxExact memory domain bigEndian address byte = some result) :
    result point = memory point := by
  cases value : memory (riscvByteAlignHOL address) with
  | loc first second => simp [memStoreByteAuxExact,value] at stored
  | word word =>
    by_cases inside : domain (riscvByteAlignHOL address) = true
    · simp only [memStoreByteAuxExact,value,inside,ite_true,Option.some.injEq] at stored
      rw [← stored]
      simp [different]
    · simp [memStoreByteAuxExact,value,inside] at stored

/-- Flapjack factoring of the native byte-load clauses: a successful load
establishes aligned-address domain membership, without an alignment premise. -/
private theorem loadDomain {width : Nat} [NeZero width]
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (bigEndian : Bool) (address : BitVec width) (byte : BitVec 8)
    (loaded : memLoadByteAuxExact memory domain bigEndian address = some byte) :
    domain (riscvByteAlignHOL address) = true := by
  cases value : memory (riscvByteAlignHOL address) with
  | loc first second => simp [memLoadByteAuxExact,value] at loaded
  | word word =>
    by_cases inside : domain (riscvByteAlignHOL address) = true
    · exact inside
    · simp [memLoadByteAuxExact,value,inside] at loaded

/-- Native non-aligned-key law matching the original statement shape. The key is outside the image of byte
alignment; all source byte lists, memories, domains and endianness are arbitrary.
Original324-330 uses only the update key, without a numerical LOG2, alignment
idempotence, range, or minimum-byte-width premise. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml"
  "write_bytearray_IGNORE_non_aligned" (words_as_type_indexed_bitvec)]
theorem writeBytearrayIgnoreNonAligned {width : Nat} [NeZero width]
    (bytes : List (BitVec 8)) (address : BitVec width)
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (bigEndian : Bool) (point : BitVec width)
    (nonAligned : ∀ x, point ≠ riscvByteAlignHOL x) :
    writeBytearrayExact address bytes memory domain bigEndian point = memory point := by
  induction bytes generalizing address with
  | nil => rfl
  | cons byte bytes ih =>
    rw [writeBytearrayExact]
    cases stored : memStoreByteAuxExact
        (writeBytearrayExact (address + 1) bytes memory domain bigEndian)
        domain bigEndian address byte with
    | none => rfl
    | some result =>
      exact (storeOther _ result domain bigEndian address point byte
        (nonAligned address) stored).trans (ih (address + 1))

/-- Native IGNORE law matching the original statement shape, with independent readable-source and updated
memories. HOL set membership is the existing native domain Boolean being true;
the original subset/read-success/outside-domain conjunction is retained.
Original332-344 derives aligned-key membership from the successful source read
and excludes the queried key from that source domain. It needs the same
alignment in load and store, irrespective of its numerical value. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml"
  "write_bytearray_IGNORE" (words_as_type_indexed_bitvec)]
theorem writeBytearrayIgnore {width : Nat} [NeZero width]
    (bytes : List (BitVec 8)) (address : BitVec width) (readBytes : List (BitVec 8))
    (point : BitVec width) (source memory : BitVec width → WordLocW width)
    (sourceDomain domain : BitVec width → Bool) (bigEndian : Bool)
    (original : (∀ x, sourceDomain x = true → domain x = true) ∧
      readBytearrayWordHOL address bytes.length
        (memLoadByteAuxExact source sourceDomain bigEndian) = some readBytes ∧
      sourceDomain point = false) :
    writeBytearrayExact address bytes memory domain bigEndian point = memory point := by
  induction bytes generalizing address readBytes with
  | nil => rfl
  | cons byte bytes ih =>
    cases loaded : memLoadByteAuxExact source sourceDomain bigEndian address with
    | none => simp [readBytearrayWordHOL,loaded] at original
    | some first =>
      cases readTail : readBytearrayWordHOL (address + 1) bytes.length
          (memLoadByteAuxExact source sourceDomain bigEndian) with
      | none =>
        simp only [List.length_cons,readBytearrayWordHOL,loaded,readTail] at original
        simp at original
      | some rest =>
        have inside := loadDomain source sourceDomain bigEndian address first loaded
        have different : point ≠ riscvByteAlignHOL address := by
          intro equal
          rw [equal,inside] at original
          simp at original
        have tail := ih (address + 1) rest ⟨original.1,readTail,original.2.2⟩
        rw [writeBytearrayExact]
        cases stored : memStoreByteAuxExact
            (writeBytearrayExact (address + 1) bytes memory domain bigEndian)
            domain bigEndian address byte with
        | none => rfl
        | some result =>
          exact (storeOther _ result domain bigEndian address point byte different stored).trans tail

/-- Native equality law matching the original statement shape. The readable domain, source/target memory
correspondence on it, original read success and initial point equality are
retained. No target read, aligned-key, or successful-store premise is added.
Original346-370 compares the tail writes at the same symbolic aligned key
and then their identical updates. No numerical LOG2/alignment fact is used;
this is the arbitrary-positive-width numerical instance of that statement. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml"
  "write_bytearray_EQ" (words_as_type_indexed_bitvec)]
theorem writeBytearrayEq {width : Nat} [NeZero width]
    (bytes : List (BitVec 8)) (address : BitVec width)
    (source memory : BitVec width → WordLocW width) (readBytes : List (BitVec 8))
    (point : BitVec width) (sourceDomain domain : BitVec width → Bool) (bigEndian : Bool)
    (original : (∀ x, sourceDomain x = true → domain x = true) ∧
      (∀ x, sourceDomain x = true → source x = memory x ∧ domain x = true) ∧
      readBytearrayWordHOL address bytes.length
        (memLoadByteAuxExact source sourceDomain bigEndian) = some readBytes ∧
      source point = memory point) :
    writeBytearrayExact address bytes source sourceDomain bigEndian point =
      writeBytearrayExact address bytes memory domain bigEndian point := by
  induction bytes generalizing address readBytes point with
  | nil => exact original.2.2.2
  | cons byte bytes ih =>
    cases loaded : memLoadByteAuxExact source sourceDomain bigEndian address with
    | none => simp [readBytearrayWordHOL,loaded] at original
    | some first =>
      cases readTail : readBytearrayWordHOL (address + 1) bytes.length
          (memLoadByteAuxExact source sourceDomain bigEndian) with
      | none =>
        simp only [List.length_cons,readBytearrayWordHOL,loaded,readTail] at original
        simp at original
      | some rest =>
        have inside := loadDomain source sourceDomain bigEndian address first loaded
        have aligned := original.2.1 _ inside
        have tailAligned := ih (address + 1) rest (riscvByteAlignHOL address)
          ⟨original.1,original.2.1,readTail,aligned.1⟩
        have tailPoint := ih (address + 1) rest point
          ⟨original.1,original.2.1,readTail,original.2.2.2⟩
        simp only [writeBytearrayExact,memStoreByteAuxExact]
        rw [← tailAligned]
        cases value : writeBytearrayExact (address + 1) bytes source sourceDomain bigEndian
            (riscvByteAlignHOL address) with
        | loc first second => exact original.2.2.2
        | word word =>
          simp only [inside,aligned.2,ite_true]
          by_cases equal : point = riscvByteAlignHOL address
          · simp [equal]
          · simpa only [if_neg equal] using tailPoint

end Flapjack.Compiler.Backend.StackRemove
