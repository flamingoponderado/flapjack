import Flapjack.Pancake.Semantics.PanSem.ShMemExact
import Flapjack.Pancake.Semantics.CrepSem.TotalEval

/-!
# Byte-list bridge between the exact Pan and Crep shared-memory primitives

The exact Pan `shMemLoadHOLExact`/`shMemStoreHOLExact`
(`Flapjack/Pancake/Semantics/PanSem/ShMemExact.lean`) hand the FFI the
little-endian byte encoding `panWordToBytesHOL w false`, while the exact Crep
`crepShMemLoadExactHOL`/`crepShMemStoreExactHOL`
(`Flapjack/Pancake/Semantics/CrepSem/EvaluateHOL.lean`) hand it
`(crepClockWordToBytes w).map UInt8.toBitVec`.  This file proves these two byte
lists are equal for every positive width, so the two primitives issue the same
`call_FFI` request whenever their FFI states and domains agree.

This is Flapjack-specific bridge infrastructure for the `pc_compile_correct`
ShMemLoad/ShMemStore cases; it has no standalone HOL declaration and therefore
no `@[hol]` tag.  The remaining obligation of that bridge (the decoded
`word_of_bytes` result and the `locals_rel` slot maintenance) is tracked by
`flapjack-pxn.18.4.3.111.1`.
-/

namespace Flapjack

/-- The little-endian byte encodings used by the exact Pan and Crep
    shared-memory primitives coincide: `panWordToBytesHOL w false` (index
    `i` is HOL `get_byte` at address `i`, little-endian) equals
    `(crepClockWordToBytes w).map UInt8.toBitVec` (index `i` is
    `(w.toNat / 256 ^ i) % 256`). -/
theorem panWordToBytesHOL_eq_map_crepClockWordToBytes {width : Nat} [NeZero width]
    (value : RiscV.Word width) :
    panWordToBytesHOL value false = (crepClockWordToBytes value).map UInt8.toBitVec := by
  unfold panWordToBytesHOL crepClockWordToBytes
  rw [List.map_map]
  apply List.map_congr_left
  intro index hindex
  simp only [Function.comp_apply]
  have hidxlt : index < width / 8 := List.mem_range.mp hindex
  have htoNat : (BitVec.ofNat width index).toNat = index := by
    have h2 : width < 2 ^ width := Nat.lt_two_pow_self
    have h1 : width / 8 ≤ width := Nat.div_le_self _ _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hidx : (BitVec.ofNat width index).toNat % (width / 8) = index := by
    rw [htoNat, Nat.mod_eq_of_lt hidxlt]
  have hexp : 256 ^ index = 2 ^ (8 * index) := by
    rw [show (256 : Nat) = 2 ^ 8 by decide]
    rw [← Nat.pow_mul]
  simp only [panGetByteHOL, Bool.false_eq_true, if_false, hidx,
    UInt8.toNat_ofNat', Nat.mod_mod]
  rw [hexp, UInt8.toBitVec_ofNat']

/-- The Pan shared-memory load issues the same `call_FFI` request as the exact
    Crep shared-memory load: for equal FFI states, byte count and address the
    (mapped-read) oracle receives identical byte lists. -/
theorem callFFIHOL_sharedMemRead_eq {width : Nat} [NeZero width] {σ : Type}
    (ffi : HolFfiState σ) (nb : Nat) (address : RiscV.Word width) :
    callFFIHOL ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 nb]
        (panWordToBytesHOL address false) =
      callFFIHOL ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 nb]
        ((crepClockWordToBytes address).map UInt8.toBitVec) := by
  rw [panWordToBytesHOL_eq_map_crepClockWordToBytes]

/-- The Pan shared-memory store issues the same `call_FFI` request as the exact
    Crep shared-memory store for the whole-word (`nb = 0`) encoding: for equal
    FFI states the (mapped-write) oracle receives identical byte lists. -/
theorem callFFIHOL_sharedMemWrite_eq {width : Nat} [NeZero width] {σ : Type}
    (ffi : HolFfiState σ) (nb : Nat) (value address : RiscV.Word width) :
    callFFIHOL ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 nb]
        (panWordToBytesHOL value false ++ panWordToBytesHOL address false) =
      callFFIHOL ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 nb]
        ((crepClockWordToBytes value ++ crepClockWordToBytes address).map
          UInt8.toBitVec) := by
  rw [panWordToBytesHOL_eq_map_crepClockWordToBytes value,
    panWordToBytesHOL_eq_map_crepClockWordToBytes address, List.map_append]

/-- The Pan shared-memory store's byte-aligned-prefix (`nb ≠ 0`) request also
    agrees with the exact Crep request: the `TAKE nb` prefix is mapped through
    the same byte encoding. -/
theorem callFFIHOL_sharedMemWrite_take_eq {width : Nat} [NeZero width] {σ : Type}
    (ffi : HolFfiState σ) (nb : Nat) (value address : RiscV.Word width) :
    callFFIHOL ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 nb]
        ((panWordToBytesHOL value false).take nb ++ panWordToBytesHOL address false) =
      callFFIHOL ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 nb]
        (((crepClockWordToBytes value).take nb ++ crepClockWordToBytes address).map
          UInt8.toBitVec) := by
  rw [panWordToBytesHOL_eq_map_crepClockWordToBytes value,
    panWordToBytesHOL_eq_map_crepClockWordToBytes address, List.map_append,
    ← List.map_take]

end Flapjack
