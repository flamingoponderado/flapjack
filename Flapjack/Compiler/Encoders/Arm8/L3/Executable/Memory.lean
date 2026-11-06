import Flapjack.Compiler.Encoders.Arm8.L3.Executable.Guards
import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Mem

/-!
# Load/store fields, words and guards for the L3 byte bridge

`Arm8.encodeInsn32` picks one of three encodings for a load or store: the
scaled twelve-bit form when the offset is a small unsigned multiple of the
access size, the nine-bit signed form when the offset is the sign extension of
its low nine bits, and `none` (four zero bytes) otherwise.

This module supplies the field, word and guard lemmas that the per-instruction
byte equality for `LoadStoreImmediate` will need; it does not itself state that
equality.  In particular it shows that the computable encoder's twelve- and
nine-bit offset fields are the L3 `holWordExtract`, that `Arm8.fields` builds
the reviewed `arm8LoadStoreImm12Word`/`arm8LoadStoreImm9Word`, and that the
computable scaled-offset and sign-extension guards are the guards the L3
`Encode` tests (`fitsSigned_iff_signExtend` for the nine-bit form).

No new HOL claim is introduced: the lemmas relate two Lean renderings of the
same field and guard computations.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8 Compiler.Encoders.Asm Compiler.Encoders.AsmSem

/-- A `Nat` truncation carried onto the 64-bit word: this is how the
computable encoder spells the L3 `setWidth` of a shifted offset. -/
theorem ofNat64_mod_setWidth (w : Nat) (v : Nat) :
    BitVec.ofNat 64 (v % 2 ^ w) = (BitVec.ofNat w v).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]

/-- The scaled twelve-bit offset of the computable encoder is the L3
`holWordExtract 12 11 0`. -/
theorem imm12_eq (k : Nat) (v : BitVec 64) :
    BitVec.ofNat 64 ((v >>> k).toNat % 4096) =
      BitVec.setWidth 64 (holWordExtract 12 11 0 (v >>> k)) := by
  simp only [holWordExtract]
  rw [holWordExtract_eq_setWidth 12 (a := 64) 11 0 (v >>> k) (by omega) (by omega) (by omega)]
  exact ofNat64_mod_setWidth 12 ((v >>> k).toNat)

/-- The twelve-bit field itself is the L3 `holWordExtract`. -/
theorem imm12Word_eq (v : BitVec 64) :
    BitVec.ofNat 12 (v.toNat % 4096) = holWordExtract 12 11 0 v := by
  simp only [holWordExtract]
  rw [holWordExtract_eq_setWidth 12 (a := 64) 11 0 v (by omega) (by omega) (by omega)]
  simp only [BitVec.ushiftRight_zero]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  omega

/-- The nine-bit field is the L3 `holWordExtract`. -/
theorem imm9Word_eq (v : BitVec 64) :
    BitVec.ofNat 9 (v.toNat % 512) = holWordExtract 9 8 0 v := by
  simp only [holWordExtract]
  rw [holWordExtract_eq_setWidth 9 (a := 64) 8 0 v (by omega) (by omega) (by omega)]
  simp only [BitVec.ushiftRight_zero]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  omega

/-- The nine-bit offset of the computable encoder is the L3 `holWordExtract`. -/
theorem imm9_eq (v : BitVec 64) :
    BitVec.ofNat 32 (v.toNat % 512) = (holWordExtract 9 8 0 v).setWidth 32 := by
  simp only [holWordExtract]
  rw [holWordExtract_eq_setWidth 9 (a := 64) 8 0 v (by omega) (by omega) (by omega)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.ushiftRight_zero]

/-- `fields` builds the L3 scaled twelve-bit word. -/
theorem fields_loadStoreImm12 (size opc imm12 rn rt : Nat) :
    fields [(2, size), (6, 57), (2, opc), (12, imm12), (5, rn), (5, rt)] =
      arm8LoadStoreImm12Word (BitVec.ofNat 2 size) (BitVec.ofNat 2 opc)
        (BitVec.ofNat 12 imm12) (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rt) := by
  simp only [fields, List.foldl_cons, List.foldl_nil, arm8LoadStoreImm12Word]
  rw [ofNat_mod_setWidth 2, ofNat_mod_setWidth 6, ofNat_mod_setWidth 2,
    ofNat_mod_setWidth 12, ofNat_mod_setWidth 5, ofNat_mod_setWidth 5]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat,
    BitVec.getLsbD_append, BitVec.getLsbD_setWidth]
  interval_cases i <;> simp

/-- `fields` builds the L3 nine-bit word. -/
theorem fields_loadStoreImm9 (size opc imm9 rn rt : Nat) :
    fields [(2, size), (6, 56), (2, opc), (1, 0), (9, imm9), (1, 0), (1, 0),
      (5, rn), (5, rt)] =
      arm8LoadStoreImm9Word (BitVec.ofNat 2 size) (BitVec.ofNat 2 opc)
        (BitVec.ofNat 9 imm9) (BitVec.ofNat 1 0) (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rt) := by
  simp only [fields, List.foldl_cons, List.foldl_nil, arm8LoadStoreImm9Word]
  rw [ofNat_mod_setWidth 2, ofNat_mod_setWidth 6, ofNat_mod_setWidth 2,
    ofNat_mod_setWidth 1, ofNat_mod_setWidth 9, ofNat_mod_setWidth 5, ofNat_mod_setWidth 5]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat,
    BitVec.getLsbD_append, BitVec.getLsbD_setWidth]
  interval_cases i <;> simp

/-- The scaled-offset guard of the computable encoder is the L3 guard. -/
theorem loadStoreGuard12_eq (k : Nat) (u : Bool) (v : BitVec 64) :
    (u && v = (BitVec.ofNat 64 ((v >>> k).toNat % 4096)) <<< k) =
      (u && (v == (BitVec.setWidth 64 (holWordExtract 12 11 0 (v >>> k))) <<< k)) := by
  rw [imm12_eq k v]
  cases u <;> rfl

/-- The nine-bit guard of the computable encoder is the L3 guard. -/
theorem loadStoreGuard9_eq (v : BitVec 64) :
    fitsSigned 9 v = (v == BitVec.signExtend 64 (holWordExtract 9 8 0 v)) := by
  have h : holWordExtract 9 8 0 v = BitVec.setWidth 9 v := by
    simp only [holWordExtract]
    rw [holWordExtract_eq_setWidth 9 (a := 64) 8 0 v (by omega) (by omega) (by omega)]
    simp only [BitVec.ushiftRight_zero]
  rw [h]
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq]
  exact fitsSigned_iff_signExtend 9 (by omega) (by omega) v

end Flapjack.Compiler.Encoders.Arm8.L3
