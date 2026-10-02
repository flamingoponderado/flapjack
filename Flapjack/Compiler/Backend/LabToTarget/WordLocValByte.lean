import Flapjack.Compiler.Backend.LabToTarget.WordLocation
import Flapjack.Misc.Alignment
import Flapjack.Byte

namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack

/-- Literal original memory byte conversion over the actual word/location
value and nested label maps. All positive dimensions and memory/endian inputs
are retained. The reviewed holByteAlign uses the specified global holLOG2:
LOG2(0) remains unconstrained at widths 1–7. This declares no equivalence to the
production panByteAlignHOL completion, whose correspondence remains open. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "word_loc_val_byte_def" (words_as_type_indexed_bitvec)]
noncomputable def wordLocValByte {width : Nat} [NeZero width] (p : BitVec width)
    (labs : Spt (Spt Nat)) (memory : BitVec width → WordLocW width)
    (address : BitVec width) (bigEndian : Bool) : Option (BitVec 8) :=
  match wordLocVal p labs (memory (holByteAlign address)) with
  | some value => some (HolByte.getByte address value bigEndian)
  | none => none

/-- Full source equation as an unconditional native kernel consumer;
Flapjack infrastructure, not a separately claimed HOL theorem. -/
theorem wordLocValByte_eq {width : Nat} [NeZero width] (p : BitVec width)
    (labs : Spt (Spt Nat)) (memory : BitVec width → WordLocW width)
    (address : BitVec width) (bigEndian : Bool) :
    wordLocValByte p labs memory address bigEndian =
      match wordLocVal p labs (memory (holByteAlign address)) with
      | some value => some (HolByte.getByte address value bigEndian)
      | none => none := rfl

/-- Generic word-memory case, with actual aligned memory lookup;
Flapjack infrastructure with no independent HOL theorem original. -/
theorem wordLocValByte_word {width : Nat} [NeZero width] (p : BitVec width)
    (labs : Spt (Spt Nat)) (memory : BitVec width → WordLocW width)
    (address value : BitVec width) (bigEndian : Bool)
    (h : memory (holByteAlign address) = .word value) :
    wordLocValByte p labs memory address bigEndian =
      some (HolByte.getByte address value bigEndian) := by
  simp [wordLocValByte, h, wordLocVal]

/-- Generic real location-hit memory case, retaining modular base/offset
arithmetic; Flapjack infrastructure with no independent HOL theorem original. -/
theorem wordLocValByte_loc_hit {width : Nat} [NeZero width] (p : BitVec width)
    (labs : Spt (Spt Nat)) (memory : BitVec width → WordLocW width)
    (address : BitVec width) (bigEndian : Bool) (k1 k2 q : Nat)
    (hm : memory (holByteAlign address) = .loc k1 k2)
    (hl : labLookup k1 k2 labs = some q) :
    wordLocValByte p labs memory address bigEndian =
      some (HolByte.getByte address (p + BitVec.ofNat width q) bigEndian) := by
  simp [wordLocValByte, hm, wordLocVal, hl]

/-- Generic location miss preserves NONE after actual aligned memory lookup;
Flapjack infrastructure with no independent HOL theorem original. -/
theorem wordLocValByte_loc_miss {width : Nat} [NeZero width] (p : BitVec width)
    (labs : Spt (Spt Nat)) (memory : BitVec width → WordLocW width)
    (address : BitVec width) (bigEndian : Bool) (k1 k2 : Nat)
    (hm : memory (holByteAlign address) = .loc k1 k2)
    (hl : labLookup k1 k2 labs = none) :
    wordLocValByte p labs memory address bigEndian = none := by
  simp [wordLocValByte, hm, wordLocVal, hl]

/-- At one-bit width the literal global LOG2(0) remains in the memory
address. Flapjack infrastructure: no chosen completion or production equality. -/
theorem wordLocValByte_oneBit_symbolic (p : BitVec 1) (labs : Spt (Spt Nat))
    (memory : BitVec 1 → WordLocW 1) (address : BitVec 1) (bigEndian : Bool) :
    wordLocValByte p labs memory address bigEndian =
      match wordLocVal p labs (memory (holAlign (holLOG2 0) address)) with
      | some value => some (HolByte.getByte address value bigEndian)
      | none => none := by
  simp only [wordLocValByte, holByteAlign, Nat.reduceDiv]
  cases wordLocVal p labs (memory (holAlign (holLOG2 0) address)) <;> rfl

end Flapjack.Compiler.Backend.LabToTarget
