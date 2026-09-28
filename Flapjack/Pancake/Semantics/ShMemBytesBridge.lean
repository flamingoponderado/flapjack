import Flapjack.Pancake.Semantics.PanSem.ShMemExact
import Flapjack.Pancake.Semantics.CrepSem.TotalEval
import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL

/-!
# Byte-list bridge between the exact Pan and Crep shared-memory primitives

The exact Pan `shMemLoadHOLExact`/`shMemStoreHOLExact`
(`Flapjack/Pancake/Semantics/PanSem/ShMemExact.lean`) hand the FFI the
little-endian byte encoding `panWordToBytesHOL w false`, while the exact Crep
`crepShMemLoadExactHOL`/`crepShMemStoreExactHOL`
(`Flapjack/Pancake/Semantics/CrepSem/EvaluateHOL.lean`) hand it
`(crepClockWordToBytes w).map UInt8.toBitVec`.  This file proves these two byte
lists are equal for every positive width, so the two primitives issue the same
`call_FFI` request whenever their FFI states and domains agree, and derives the
result correspondence of the two primitives: the same `.finalFfi` oracle event,
the same `.error`, or the same successful `none` (the `.ret` FFI-return case).

This is Flapjack-specific bridge infrastructure for the `pc_compile_correct`
ShMemLoad/ShMemStore cases; it has no standalone HOL declaration and therefore
no `@[hol]` tag.  The remaining obligations of that bridge are still tracked by
`flapjack-pxn.18.4.3.111.1`: the decoded `word_of_bytes` equality (the value
installed on a `.ret`) and the `locals_rel` slot maintenance of the written
variable.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS)

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

/-- Result correspondence of the exact Pan and Crep shared-memory loads: for
    equal FFI states and domains the two primitives agree on the FFI oracle
    event (`some (.finalFfi e)`), on `.error`, or on the successful `none`
    (FFI-returned) case.  The `.ret` branch leaves the decoded value and the
    written variable for the `locals_rel` slot obligation (see the module
    docstring). -/
theorem shMemLoadHOLExact_control_corresponds {width : Nat} [NeZero width] {σ : Type}
    (source : PanSemStateExact width σ) [DecidablePred source.shMemaddrs]
    (target : CrepSemHOLState width σ) [DecidablePred target.shMemaddrs]
    (kind : VarKind) (name : MlS) (crepName : Nat) (address : RiscV.Word width) (nb : Nat)
    (hffi : source.ffi = target.ffi)
    (hdom : ∀ a, source.shMemaddrs a = target.shMemaddrs a) :
    (∃ e : HolFinalEvent, (shMemLoadHOLExact source kind name address nb).1 = some (.finalFfi e) ∧
        (crepShMemLoadExactHOL crepName address nb target).1 = some (.finalFfi e)) ∨
      ((shMemLoadHOLExact source kind name address nb).1 = some .error ∧
        (crepShMemLoadExactHOL crepName address nb target).1 = some .error) ∨
      ((shMemLoadHOLExact source kind name address nb).1 = none ∧
        (crepShMemLoadExactHOL crepName address nb target).1 = none) := by
  unfold shMemLoadHOLExact crepShMemLoadExactHOL
  rw [hffi, panWordToBytesHOL_eq_map_crepClockWordToBytes address]
  simp only [hdom]
  split
  · split
    · cases hcall : callFFIHOL target.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 nb]
          ((crepClockWordToBytes address).map UInt8.toBitVec) with
      | final event => exact Or.inl ⟨event, rfl, rfl⟩
      | ret newFfi newBytes => exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · split
    · cases hcall : callFFIHOL target.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 nb]
          ((crepClockWordToBytes address).map UInt8.toBitVec) with
      | final event => exact Or.inl ⟨event, rfl, rfl⟩
      | ret newFfi newBytes => exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)

/-- Result correspondence of the exact Pan and Crep shared-memory stores: for
    equal FFI states and domains, and a target local holding the stored word,
    the two primitives agree on the FFI oracle event, on `.error`, or on the
    successful `none` case. -/
theorem shMemStoreHOLExact_control_corresponds {width : Nat} [NeZero width] {σ : Type}
    (source : PanSemStateExact width σ) [DecidablePred source.shMemaddrs]
    (target : CrepSemHOLState width σ) [DecidablePred target.shMemaddrs]
    (word : RiscV.Word width) (crepName : Nat) (address : RiscV.Word width) (nb : Nat)
    (hffi : source.ffi = target.ffi)
    (hdom : ∀ a, source.shMemaddrs a = target.shMemaddrs a)
    (hlocal : target.locals.lookup crepName = some (.word word)) :
    (∃ e : HolFinalEvent, (shMemStoreHOLExact source word address nb).1 = some (.finalFfi e) ∧
        (crepShMemStoreExactHOL crepName address nb target).1 = some (.finalFfi e)) ∨
      ((shMemStoreHOLExact source word address nb).1 = some .error ∧
        (crepShMemStoreExactHOL crepName address nb target).1 = some .error) ∨
      ((shMemStoreHOLExact source word address nb).1 = none ∧
        (crepShMemStoreExactHOL crepName address nb target).1 = none) := by
  unfold shMemStoreHOLExact crepShMemStoreExactHOL
  simp only [hlocal]
  rw [hffi, panWordToBytesHOL_eq_map_crepClockWordToBytes word,
    panWordToBytesHOL_eq_map_crepClockWordToBytes address]
  simp only [List.map_append, ← List.map_take]
  simp only [hdom]
  split
  · split
    · cases hcall : callFFIHOL target.ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 nb]
          (List.map UInt8.toBitVec (crepClockWordToBytes word) ++
            List.map UInt8.toBitVec (crepClockWordToBytes address)) with
      | final event => exact Or.inl ⟨event, rfl, rfl⟩
      | ret newFfi newBytes => exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · split
    · cases hcall : callFFIHOL target.ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 nb]
          (List.map UInt8.toBitVec (List.take nb (crepClockWordToBytes word)) ++
            List.map UInt8.toBitVec (crepClockWordToBytes address)) with
      | final event => exact Or.inl ⟨event, rfl, rfl⟩
      | ret newFfi newBytes => exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)

end Flapjack
