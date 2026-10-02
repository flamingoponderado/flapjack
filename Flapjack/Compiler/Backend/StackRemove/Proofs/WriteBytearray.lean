import Flapjack.Compiler.Backend.Semantics.WordSem
import Flapjack.Pancake.Semantics.LoopSem

/- Source-review pending for the three original write_bytearray support/equality laws.
The native alignment uses Nat.log2 (width / 8); HOL LOG2 0 is unspecified by
its positive-argument specification. These proofs do not inspect that numerical
choice, but correspondence of the imported operators at widths below eight is
not established here. No HOL port tags are claimed pending that review. -/

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
alignment; all source byte lists, memories, domains and endianness are arbitrary. -/
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
the original subset/read-success/outside-domain conjunction is retained. -/
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
retained. No target read, aligned-key, or successful-store premise is added. -/
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
