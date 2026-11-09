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

/-- The nine-bit `holWordExtract` at width nine. -/
theorem h9w_eq (offset : BitVec 64) :
    holWordExtract 9 8 0 offset = BitVec.setWidth 9 offset := by
  simp only [holWordExtract]
  rw [holWordExtract_eq_setWidth 9 (a := 64) 8 0 offset (by omega) (by omega) (by omega)]
  simp only [BitVec.ushiftRight_zero]

/-- A 64-bit load encodes to the same four bytes on both sides. -/
theorem encodeBytes_loadStore64_load (unsignedOffset : Bool) (offset : BitVec 64) (rn rt : Nat) :
    encodeBytes (.loadStoreImmediate 3 false .load false unsignedOffset offset rn rt) =
      arm8Encode (.LoadStore (.«LoadStoreImmediate@64»
        ((3 : BitVec 64), false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
         false, unsignedOffset, offset, BitVec.ofNat 5 rn, BitVec.ofNat 5 rt))) := by
  have hiff12 : (offset == (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> (3 : Nat)))) <<< (3 : Nat)) =
      decide (offset = (BitVec.ofNat 64 ((offset >>> (3 : Nat)).toNat % 4096)) <<< (3 : Nat)) := by
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq, decide_eq_true_eq]
    exact Iff.intro
      (fun h => h.trans (congrArg (fun x : BitVec 64 => x <<< (3 : Nat)) (imm12_eq 3 offset).symm))
      (fun h => h.trans (congrArg (fun x : BitVec 64 => x <<< (3 : Nat)) (imm12_eq 3 offset)))
  have hiff9 : (offset == BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) =
      fitsSigned 9 offset := by
    rw [h9w_eq]
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq]
    exact (fitsSigned_iff_signExtend 9 (by omega) (by omega) offset).symm
  by_cases h12 : (unsignedOffset && decide (offset = (BitVec.ofNat 64 ((offset >>> (3 : Nat)).toNat % 4096)) <<< (3 : Nat))) = true
  · have hoff : offset = (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> (3 : Nat)))) <<< (3 : Nat) := by
      have h := of_decide_eq_true (Bool.and_eq_true_iff.mp h12).2
      calc offset = (BitVec.ofNat 64 ((offset >>> (3 : Nat)).toNat % 4096)) <<< (3 : Nat) := h
        _ = (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> (3 : Nat)))) <<< (3 : Nat) := by
            congr 1
            exact imm12_eq 3 offset
    have hu : unsignedOffset = true := (Bool.and_eq_true_iff.mp h12).1
    have hw : encodeInsn32 (.loadStoreImmediate 3 false .load false unsignedOffset offset rn rt) =
        some (fields [(2, 3), (6, 57), (2, 1), (12, ((offset >>> (3 : Nat)).toNat % 4096)),
          (5, rn), (5, rt)]) := by
      simp only [encodeInsn32]
      split
      · simp
      · exact absurd h12 ‹_›
    rw [hu] at hw
    rw [hu, encodeBytes_eq_of_encodeInsn32 _ _ hw]
    simp only [arm8Encode, arm8Encode_loadStoreImm12_load offset (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rt) hoff,
      fields_loadStoreImm12, imm12Word_eq]
    rfl
  · have hfall : (unsignedOffset && (offset == (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> (3 : Nat)))) <<< (3 : Nat))) = false := by
      cases hu : unsignedOffset
      · rfl
      · have hp : decide (offset = (BitVec.ofNat 64 ((offset >>> (3 : Nat)).toNat % 4096)) <<< (3 : Nat)) = false := by
          have h := h12
          rw [hu] at h
          simpa using h
        simp only [hiff12, hp, Bool.true_and]
    by_cases h9 : fitsSigned 9 offset = true
    · have hsx : offset = BitVec.signExtend 64 (holWordExtract 9 8 0 offset) := by
        have h : (offset == BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) = true := by
          rw [hiff9]
          exact h9
        exact beq_iff_eq.mp h
      have hw : encodeInsn32 (.loadStoreImmediate 3 false .load false unsignedOffset offset rn rt) =
          some (fields [(2, 3), (6, 56), (2, 1), (1, 0), (9, offset.toNat % 512),
            (1, 0), (1, 0), (5, rn), (5, rt)]) := by
        simp only [encodeInsn32]
        split
        · exact absurd ‹_› h12
        · simp
      rw [encodeBytes_eq_of_encodeInsn32 _ _ hw]
      simp only [arm8Encode, arm8Encode_loadStoreImm9_load offset unsignedOffset (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rt)
        hfall hsx, fields_loadStoreImm9, imm9Word_eq]
    · have h9' : (offset == BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) = false := by
        rw [hiff9]
        simpa [Bool.not_eq_true] using h9
      have hg : ¬ (unsignedOffset = true ∧ offset = (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> (3 : Nat)))) <<< (3 : Nat)) := by
        intro h
        have h' : (unsignedOffset && (offset == (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> (3 : Nat)))) <<< (3 : Nat))) = true := by
          simp only [Bool.and_eq_true_iff, beq_iff_eq]
          exact ⟨h.1, h.2⟩
        rw [h'] at hfall
        exact absurd hfall (by decide)
      have hs : BitVec.setWidth 2 (3 : BitVec 64) = BitVec.ofNat 2 3 := by decide
      have h3 : (BitVec.ofNat 2 3).toNat = 3 := by decide
      have hload : (MemOp.MemOp_LOAD == MemOp.MemOp_LOAD) = true := by decide
      have hnrm : (AccType.AccType_NORMAL == AccType.AccType_NORMAL) = true := by decide
      have hpref : (MemOp.MemOp_LOAD == MemOp.MemOp_PREFETCH) = false := by decide
      have hstore : (MemOp.MemOp_LOAD == MemOp.MemOp_STORE) = false := by decide
      have hnf : ((!false : Bool) = true) := rfl
      have hw : encodeInsn32 (.loadStoreImmediate 3 false .load false unsignedOffset offset rn rt) =
          none := by
        simp only [encodeInsn32]
        split
        · exact absurd ‹_› h12
        · rfl
      rw [encodeBytes_eq_of_encodeInsn32_none _ hw]
      simp only [arm8Encode, Encode, e_load_store, e_LoadStoreImmediate, hs, h3, hload, hnrm,
        hpref, Bool.false_eq_true, if_false, hnf, if_true, Bool.and_true,
        Bool.and_eq_true_iff, beq_iff_eq, hg, h9']

/-- A 64-bit store encodes to the same four bytes on both sides. -/
theorem encodeBytes_loadStore64_store (unsignedOffset : Bool) (offset : BitVec 64) (rn rt : Nat) :
    encodeBytes (.loadStoreImmediate 3 false .store false unsignedOffset offset rn rt) =
      arm8Encode (.LoadStore (.«LoadStoreImmediate@64»
        ((3 : BitVec 64), false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
         false, unsignedOffset, offset, BitVec.ofNat 5 rn, BitVec.ofNat 5 rt))) := by
  have hiff12 : (offset == (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> (3 : Nat)))) <<< (3 : Nat)) =
      decide (offset = (BitVec.ofNat 64 ((offset >>> (3 : Nat)).toNat % 4096)) <<< (3 : Nat)) := by
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq, decide_eq_true_eq]
    exact Iff.intro
      (fun h => h.trans (congrArg (fun x : BitVec 64 => x <<< (3 : Nat)) (imm12_eq 3 offset).symm))
      (fun h => h.trans (congrArg (fun x : BitVec 64 => x <<< (3 : Nat)) (imm12_eq 3 offset)))
  have hiff9 : (offset == BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) =
      fitsSigned 9 offset := by
    rw [h9w_eq]
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq]
    exact (fitsSigned_iff_signExtend 9 (by omega) (by omega) offset).symm
  by_cases h12 : (unsignedOffset && decide (offset = (BitVec.ofNat 64 ((offset >>> (3 : Nat)).toNat % 4096)) <<< (3 : Nat))) = true
  · have hoff : offset = (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> (3 : Nat)))) <<< (3 : Nat) := by
      have h := of_decide_eq_true (Bool.and_eq_true_iff.mp h12).2
      calc offset = (BitVec.ofNat 64 ((offset >>> (3 : Nat)).toNat % 4096)) <<< (3 : Nat) := h
        _ = (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> (3 : Nat)))) <<< (3 : Nat) := by
            congr 1
            exact imm12_eq 3 offset
    have hu : unsignedOffset = true := (Bool.and_eq_true_iff.mp h12).1
    have hw : encodeInsn32 (.loadStoreImmediate 3 false .store false unsignedOffset offset rn rt) =
        some (fields [(2, 3), (6, 57), (2, 0), (12, ((offset >>> (3 : Nat)).toNat % 4096)),
          (5, rn), (5, rt)]) := by
      simp only [encodeInsn32]
      split
      · simp
      · exact absurd h12 ‹_›
    rw [hu] at hw
    rw [hu, encodeBytes_eq_of_encodeInsn32 _ _ hw]
    simp only [arm8Encode, arm8Encode_loadStoreImm12_store offset (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rt) hoff,
      fields_loadStoreImm12, imm12Word_eq]
    rfl
  · have hfall : (unsignedOffset && (offset == (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> (3 : Nat)))) <<< (3 : Nat))) = false := by
      cases hu : unsignedOffset
      · rfl
      · have hp : decide (offset = (BitVec.ofNat 64 ((offset >>> (3 : Nat)).toNat % 4096)) <<< (3 : Nat)) = false := by
          have h := h12
          rw [hu] at h
          simpa using h
        simp only [hiff12, hp, Bool.true_and]
    by_cases h9 : fitsSigned 9 offset = true
    · have hsx : offset = BitVec.signExtend 64 (holWordExtract 9 8 0 offset) := by
        have h : (offset == BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) = true := by
          rw [hiff9]
          exact h9
        exact beq_iff_eq.mp h
      have hw : encodeInsn32 (.loadStoreImmediate 3 false .store false unsignedOffset offset rn rt) =
          some (fields [(2, 3), (6, 56), (2, 0), (1, 0), (9, offset.toNat % 512),
            (1, 0), (1, 0), (5, rn), (5, rt)]) := by
        simp only [encodeInsn32]
        split
        · exact absurd ‹_› h12
        · simp
      rw [encodeBytes_eq_of_encodeInsn32 _ _ hw]
      simp only [arm8Encode, arm8Encode_loadStoreImm9_store offset unsignedOffset (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rt)
        hfall hsx, fields_loadStoreImm9, imm9Word_eq]
    · have h9' : (offset == BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) = false := by
        rw [hiff9]
        simpa [Bool.not_eq_true] using h9
      have hg : ¬ (unsignedOffset = true ∧ offset = (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> (3 : Nat)))) <<< (3 : Nat)) := by
        intro h
        have h' : (unsignedOffset && (offset == (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> (3 : Nat)))) <<< (3 : Nat))) = true := by
          simp only [Bool.and_eq_true_iff, beq_iff_eq]
          exact ⟨h.1, h.2⟩
        rw [h'] at hfall
        exact absurd hfall (by decide)
      have hs : BitVec.setWidth 2 (3 : BitVec 64) = BitVec.ofNat 2 3 := by decide
      have h3 : (BitVec.ofNat 2 3).toNat = 3 := by decide
      have hload : (MemOp.MemOp_STORE == MemOp.MemOp_STORE) = true := by decide
      have hnrm : (AccType.AccType_NORMAL == AccType.AccType_NORMAL) = true := by decide
      have hpref : (MemOp.MemOp_STORE == MemOp.MemOp_PREFETCH) = false := by decide
      have hstore : (MemOp.MemOp_STORE == MemOp.MemOp_STORE) = true := by decide
      have hnf : ((!false : Bool) = true) := rfl
      have hw : encodeInsn32 (.loadStoreImmediate 3 false .store false unsignedOffset offset rn rt) =
          none := by
        simp only [encodeInsn32]
        split
        · exact absurd ‹_› h12
        · rfl
      rw [encodeBytes_eq_of_encodeInsn32_none _ hw]
      simp only [arm8Encode, Encode, e_load_store, e_LoadStoreImmediate, hs, h3, hload, hnrm,
        hpref, Bool.false_eq_true, if_false, hnf, if_true, Bool.and_true,
        Bool.and_eq_true_iff, beq_iff_eq, hg, h9']

/-- A 32-bit load encodes to the same four bytes on both sides. -/
theorem encodeBytes_loadStore32_load (unsignedOffset : Bool) (offset : BitVec 64) (rn rt : Nat) :
    encodeBytes (.loadStoreImmediate 2 true .load false unsignedOffset offset rn rt) =
      arm8Encode (.LoadStore (.«LoadStoreImmediate@32»
        ((BitVec.ofNat 32 2), true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
         false, unsignedOffset, offset, BitVec.ofNat 5 rn, BitVec.ofNat 5 rt))) := by
  have hiff12 : (offset == (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> (2 : Nat)))) <<< (2 : Nat)) =
      decide (offset = (BitVec.ofNat 64 ((offset >>> (2 : Nat)).toNat % 4096)) <<< (2 : Nat)) := by
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq, decide_eq_true_eq]
    exact Iff.intro
      (fun h => h.trans (congrArg (fun x : BitVec 64 => x <<< (2 : Nat)) (imm12_eq 2 offset).symm))
      (fun h => h.trans (congrArg (fun x : BitVec 64 => x <<< (2 : Nat)) (imm12_eq 2 offset)))
  have hiff9 : (offset == BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) =
      fitsSigned 9 offset := by
    rw [h9w_eq]
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq]
    exact (fitsSigned_iff_signExtend 9 (by omega) (by omega) offset).symm
  by_cases h12 : (unsignedOffset && decide (offset = (BitVec.ofNat 64 ((offset >>> (2 : Nat)).toNat % 4096)) <<< (2 : Nat))) = true
  · have hoff : offset = (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> (2 : Nat)))) <<< (2 : Nat) := by
      have h := of_decide_eq_true (Bool.and_eq_true_iff.mp h12).2
      calc offset = (BitVec.ofNat 64 ((offset >>> (2 : Nat)).toNat % 4096)) <<< (2 : Nat) := h
        _ = (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> (2 : Nat)))) <<< (2 : Nat) := by
            congr 1
            exact imm12_eq 2 offset
    have hu : unsignedOffset = true := (Bool.and_eq_true_iff.mp h12).1
    have hw : encodeInsn32 (.loadStoreImmediate 2 true .load false unsignedOffset offset rn rt) =
        some (fields [(2, 2), (6, 57), (2, 1), (12, ((offset >>> (2 : Nat)).toNat % 4096)),
          (5, rn), (5, rt)]) := by
      simp only [encodeInsn32]
      split
      · simp
      · exact absurd h12 ‹_›
    rw [hu] at hw
    rw [hu, encodeBytes_eq_of_encodeInsn32 _ _ hw]
    simp only [arm8Encode, arm8Encode_loadStoreImm12_load32 offset (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rt) hoff,
      fields_loadStoreImm12, imm12Word_eq]
    rfl
  · have hfall : (unsignedOffset && (offset == (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> (2 : Nat)))) <<< (2 : Nat))) = false := by
      cases hu : unsignedOffset
      · rfl
      · have hp : decide (offset = (BitVec.ofNat 64 ((offset >>> (2 : Nat)).toNat % 4096)) <<< (2 : Nat)) = false := by
          have h := h12
          rw [hu] at h
          simpa using h
        simp only [hiff12, hp, Bool.true_and]
    by_cases h9 : fitsSigned 9 offset = true
    · have hsx : offset = BitVec.signExtend 64 (holWordExtract 9 8 0 offset) := by
        have h : (offset == BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) = true := by
          rw [hiff9]
          exact h9
        exact beq_iff_eq.mp h
      have hw : encodeInsn32 (.loadStoreImmediate 2 true .load false unsignedOffset offset rn rt) =
          some (fields [(2, 2), (6, 56), (2, 1), (1, 0), (9, offset.toNat % 512),
            (1, 0), (1, 0), (5, rn), (5, rt)]) := by
        simp only [encodeInsn32]
        split
        · exact absurd ‹_› h12
        · simp
      rw [encodeBytes_eq_of_encodeInsn32 _ _ hw]
      simp only [arm8Encode, arm8Encode_loadStoreImm9_load32 offset unsignedOffset (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rt)
        hfall hsx, fields_loadStoreImm9, imm9Word_eq]
    · have h9' : (offset == BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) = false := by
        rw [hiff9]
        simpa [Bool.not_eq_true] using h9
      have hg : ¬ (unsignedOffset = true ∧ offset = (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> (2 : Nat)))) <<< (2 : Nat)) := by
        intro h
        have h' : (unsignedOffset && (offset == (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> (2 : Nat)))) <<< (2 : Nat))) = true := by
          simp only [Bool.and_eq_true_iff, beq_iff_eq]
          exact ⟨h.1, h.2⟩
        rw [h'] at hfall
        exact absurd hfall (by decide)
      have hs : BitVec.setWidth 2 (BitVec.ofNat 32 2) = BitVec.ofNat 2 2 := by decide
      have h3 : (BitVec.ofNat 2 2).toNat = 2 := by decide
      have hload : (MemOp.MemOp_LOAD == MemOp.MemOp_LOAD) = true := by decide
      have hnrm : (AccType.AccType_NORMAL == AccType.AccType_NORMAL) = true := by decide
      have hpref : (MemOp.MemOp_LOAD == MemOp.MemOp_PREFETCH) = false := by decide
      have hstore : (MemOp.MemOp_LOAD == MemOp.MemOp_STORE) = false := by decide
      have hnf : ((!false : Bool) = true) := rfl
      have hw : encodeInsn32 (.loadStoreImmediate 2 true .load false unsignedOffset offset rn rt) =
          none := by
        simp only [encodeInsn32]
        split
        · exact absurd ‹_› h12
        · rfl
      rw [encodeBytes_eq_of_encodeInsn32_none _ hw]
      simp only [arm8Encode, Encode, e_load_store, e_LoadStoreImmediate, hs, h3, hload, hnrm,
        hpref, Bool.false_eq_true, if_false, hnf, if_true, Bool.and_true,
        Bool.and_eq_true_iff, beq_iff_eq, hg, h9']

/-- A 32-bit store encodes to the same four bytes on both sides. -/
theorem encodeBytes_loadStore32_store (unsignedOffset : Bool) (offset : BitVec 64) (rn rt : Nat) :
    encodeBytes (.loadStoreImmediate 2 true .store false unsignedOffset offset rn rt) =
      arm8Encode (.LoadStore (.«LoadStoreImmediate@32»
        ((BitVec.ofNat 32 2), true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
         false, unsignedOffset, offset, BitVec.ofNat 5 rn, BitVec.ofNat 5 rt))) := by
  have hiff12 : (offset == (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> (2 : Nat)))) <<< (2 : Nat)) =
      decide (offset = (BitVec.ofNat 64 ((offset >>> (2 : Nat)).toNat % 4096)) <<< (2 : Nat)) := by
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq, decide_eq_true_eq]
    exact Iff.intro
      (fun h => h.trans (congrArg (fun x : BitVec 64 => x <<< (2 : Nat)) (imm12_eq 2 offset).symm))
      (fun h => h.trans (congrArg (fun x : BitVec 64 => x <<< (2 : Nat)) (imm12_eq 2 offset)))
  have hiff9 : (offset == BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) =
      fitsSigned 9 offset := by
    rw [h9w_eq]
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq]
    exact (fitsSigned_iff_signExtend 9 (by omega) (by omega) offset).symm
  by_cases h12 : (unsignedOffset && decide (offset = (BitVec.ofNat 64 ((offset >>> (2 : Nat)).toNat % 4096)) <<< (2 : Nat))) = true
  · have hoff : offset = (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> (2 : Nat)))) <<< (2 : Nat) := by
      have h := of_decide_eq_true (Bool.and_eq_true_iff.mp h12).2
      calc offset = (BitVec.ofNat 64 ((offset >>> (2 : Nat)).toNat % 4096)) <<< (2 : Nat) := h
        _ = (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> (2 : Nat)))) <<< (2 : Nat) := by
            congr 1
            exact imm12_eq 2 offset
    have hu : unsignedOffset = true := (Bool.and_eq_true_iff.mp h12).1
    have hw : encodeInsn32 (.loadStoreImmediate 2 true .store false unsignedOffset offset rn rt) =
        some (fields [(2, 2), (6, 57), (2, 0), (12, ((offset >>> (2 : Nat)).toNat % 4096)),
          (5, rn), (5, rt)]) := by
      simp only [encodeInsn32]
      split
      · simp
      · exact absurd h12 ‹_›
    rw [hu] at hw
    rw [hu, encodeBytes_eq_of_encodeInsn32 _ _ hw]
    simp only [arm8Encode, arm8Encode_loadStoreImm12_store32 offset (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rt) hoff,
      fields_loadStoreImm12, imm12Word_eq]
    rfl
  · have hfall : (unsignedOffset && (offset == (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> (2 : Nat)))) <<< (2 : Nat))) = false := by
      cases hu : unsignedOffset
      · rfl
      · have hp : decide (offset = (BitVec.ofNat 64 ((offset >>> (2 : Nat)).toNat % 4096)) <<< (2 : Nat)) = false := by
          have h := h12
          rw [hu] at h
          simpa using h
        simp only [hiff12, hp, Bool.true_and]
    by_cases h9 : fitsSigned 9 offset = true
    · have hsx : offset = BitVec.signExtend 64 (holWordExtract 9 8 0 offset) := by
        have h : (offset == BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) = true := by
          rw [hiff9]
          exact h9
        exact beq_iff_eq.mp h
      have hw : encodeInsn32 (.loadStoreImmediate 2 true .store false unsignedOffset offset rn rt) =
          some (fields [(2, 2), (6, 56), (2, 0), (1, 0), (9, offset.toNat % 512),
            (1, 0), (1, 0), (5, rn), (5, rt)]) := by
        simp only [encodeInsn32]
        split
        · exact absurd ‹_› h12
        · simp
      rw [encodeBytes_eq_of_encodeInsn32 _ _ hw]
      simp only [arm8Encode, arm8Encode_loadStoreImm9_store32 offset unsignedOffset (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rt)
        hfall hsx, fields_loadStoreImm9, imm9Word_eq]
    · have h9' : (offset == BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) = false := by
        rw [hiff9]
        simpa [Bool.not_eq_true] using h9
      have hg : ¬ (unsignedOffset = true ∧ offset = (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> (2 : Nat)))) <<< (2 : Nat)) := by
        intro h
        have h' : (unsignedOffset && (offset == (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> (2 : Nat)))) <<< (2 : Nat))) = true := by
          simp only [Bool.and_eq_true_iff, beq_iff_eq]
          exact ⟨h.1, h.2⟩
        rw [h'] at hfall
        exact absurd hfall (by decide)
      have hs : BitVec.setWidth 2 (BitVec.ofNat 32 2) = BitVec.ofNat 2 2 := by decide
      have h3 : (BitVec.ofNat 2 2).toNat = 2 := by decide
      have hload : (MemOp.MemOp_STORE == MemOp.MemOp_STORE) = true := by decide
      have hnrm : (AccType.AccType_NORMAL == AccType.AccType_NORMAL) = true := by decide
      have hpref : (MemOp.MemOp_STORE == MemOp.MemOp_PREFETCH) = false := by decide
      have hstore : (MemOp.MemOp_STORE == MemOp.MemOp_STORE) = true := by decide
      have hnf : ((!false : Bool) = true) := rfl
      have hw : encodeInsn32 (.loadStoreImmediate 2 true .store false unsignedOffset offset rn rt) =
          none := by
        simp only [encodeInsn32]
        split
        · exact absurd ‹_› h12
        · rfl
      rw [encodeBytes_eq_of_encodeInsn32_none _ hw]
      simp only [arm8Encode, Encode, e_load_store, e_LoadStoreImmediate, hs, h3, hload, hnrm,
        hpref, Bool.false_eq_true, if_false, hnf, if_true, Bool.and_true,
        Bool.and_eq_true_iff, beq_iff_eq, hg, h9']

/-- A 16-bit load encodes to the same four bytes on both sides. -/
theorem encodeBytes_loadStore16_load (unsignedOffset : Bool) (offset : BitVec 64) (rn rt : Nat) :
    encodeBytes (.loadStoreImmediate 1 true .load false unsignedOffset offset rn rt) =
      arm8Encode (.LoadStore (.«LoadStoreImmediate@16»
        ((BitVec.ofNat 16 1), true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
         false, unsignedOffset, offset, BitVec.ofNat 5 rn, BitVec.ofNat 5 rt))) := by
  have hiff12 : (offset == (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> (1 : Nat)))) <<< (1 : Nat)) =
      decide (offset = (BitVec.ofNat 64 ((offset >>> (1 : Nat)).toNat % 4096)) <<< (1 : Nat)) := by
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq, decide_eq_true_eq]
    exact Iff.intro
      (fun h => h.trans (congrArg (fun x : BitVec 64 => x <<< (1 : Nat)) (imm12_eq 1 offset).symm))
      (fun h => h.trans (congrArg (fun x : BitVec 64 => x <<< (1 : Nat)) (imm12_eq 1 offset)))
  have hiff9 : (offset == BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) =
      fitsSigned 9 offset := by
    rw [h9w_eq]
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq]
    exact (fitsSigned_iff_signExtend 9 (by omega) (by omega) offset).symm
  by_cases h12 : (unsignedOffset && decide (offset = (BitVec.ofNat 64 ((offset >>> (1 : Nat)).toNat % 4096)) <<< (1 : Nat))) = true
  · have hoff : offset = (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> (1 : Nat)))) <<< (1 : Nat) := by
      have h := of_decide_eq_true (Bool.and_eq_true_iff.mp h12).2
      calc offset = (BitVec.ofNat 64 ((offset >>> (1 : Nat)).toNat % 4096)) <<< (1 : Nat) := h
        _ = (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> (1 : Nat)))) <<< (1 : Nat) := by
            congr 1
            exact imm12_eq 1 offset
    have hu : unsignedOffset = true := (Bool.and_eq_true_iff.mp h12).1
    have hw : encodeInsn32 (.loadStoreImmediate 1 true .load false unsignedOffset offset rn rt) =
        some (fields [(2, 1), (6, 57), (2, 1), (12, ((offset >>> (1 : Nat)).toNat % 4096)),
          (5, rn), (5, rt)]) := by
      simp only [encodeInsn32]
      split
      · simp
      · exact absurd h12 ‹_›
    rw [hu] at hw
    rw [hu, encodeBytes_eq_of_encodeInsn32 _ _ hw]
    simp only [arm8Encode, arm8Encode_loadStoreImm12_load16 offset (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rt) hoff,
      fields_loadStoreImm12, imm12Word_eq]
    rfl
  · have hfall : (unsignedOffset && (offset == (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> (1 : Nat)))) <<< (1 : Nat))) = false := by
      cases hu : unsignedOffset
      · rfl
      · have hp : decide (offset = (BitVec.ofNat 64 ((offset >>> (1 : Nat)).toNat % 4096)) <<< (1 : Nat)) = false := by
          have h := h12
          rw [hu] at h
          simpa using h
        simp only [hiff12, hp, Bool.true_and]
    by_cases h9 : fitsSigned 9 offset = true
    · have hsx : offset = BitVec.signExtend 64 (holWordExtract 9 8 0 offset) := by
        have h : (offset == BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) = true := by
          rw [hiff9]
          exact h9
        exact beq_iff_eq.mp h
      have hw : encodeInsn32 (.loadStoreImmediate 1 true .load false unsignedOffset offset rn rt) =
          some (fields [(2, 1), (6, 56), (2, 1), (1, 0), (9, offset.toNat % 512),
            (1, 0), (1, 0), (5, rn), (5, rt)]) := by
        simp only [encodeInsn32]
        split
        · exact absurd ‹_› h12
        · simp
      rw [encodeBytes_eq_of_encodeInsn32 _ _ hw]
      simp only [arm8Encode, arm8Encode_loadStoreImm9_load16 offset unsignedOffset (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rt)
        hfall hsx, fields_loadStoreImm9, imm9Word_eq]
    · have h9' : (offset == BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) = false := by
        rw [hiff9]
        simpa [Bool.not_eq_true] using h9
      have hg : ¬ (unsignedOffset = true ∧ offset = (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> (1 : Nat)))) <<< (1 : Nat)) := by
        intro h
        have h' : (unsignedOffset && (offset == (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> (1 : Nat)))) <<< (1 : Nat))) = true := by
          simp only [Bool.and_eq_true_iff, beq_iff_eq]
          exact ⟨h.1, h.2⟩
        rw [h'] at hfall
        exact absurd hfall (by decide)
      have hs : BitVec.setWidth 2 (BitVec.ofNat 16 1) = BitVec.ofNat 2 1 := by decide
      have h3 : (BitVec.ofNat 2 1).toNat = 1 := by decide
      have hload : (MemOp.MemOp_LOAD == MemOp.MemOp_LOAD) = true := by decide
      have hnrm : (AccType.AccType_NORMAL == AccType.AccType_NORMAL) = true := by decide
      have hpref : (MemOp.MemOp_LOAD == MemOp.MemOp_PREFETCH) = false := by decide
      have hstore : (MemOp.MemOp_LOAD == MemOp.MemOp_STORE) = false := by decide
      have hnf : ((!false : Bool) = true) := rfl
      have hw : encodeInsn32 (.loadStoreImmediate 1 true .load false unsignedOffset offset rn rt) =
          none := by
        simp only [encodeInsn32]
        split
        · exact absurd ‹_› h12
        · rfl
      rw [encodeBytes_eq_of_encodeInsn32_none _ hw]
      simp only [arm8Encode, Encode, e_load_store, e_LoadStoreImmediate, hs, h3, hload, hnrm,
        hpref, Bool.false_eq_true, if_false, hnf, if_true, Bool.and_true,
        Bool.and_eq_true_iff, beq_iff_eq, hg, h9']

/-- A 16-bit store encodes to the same four bytes on both sides. -/
theorem encodeBytes_loadStore16_store (unsignedOffset : Bool) (offset : BitVec 64) (rn rt : Nat) :
    encodeBytes (.loadStoreImmediate 1 true .store false unsignedOffset offset rn rt) =
      arm8Encode (.LoadStore (.«LoadStoreImmediate@16»
        ((BitVec.ofNat 16 1), true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
         false, unsignedOffset, offset, BitVec.ofNat 5 rn, BitVec.ofNat 5 rt))) := by
  have hiff12 : (offset == (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> (1 : Nat)))) <<< (1 : Nat)) =
      decide (offset = (BitVec.ofNat 64 ((offset >>> (1 : Nat)).toNat % 4096)) <<< (1 : Nat)) := by
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq, decide_eq_true_eq]
    exact Iff.intro
      (fun h => h.trans (congrArg (fun x : BitVec 64 => x <<< (1 : Nat)) (imm12_eq 1 offset).symm))
      (fun h => h.trans (congrArg (fun x : BitVec 64 => x <<< (1 : Nat)) (imm12_eq 1 offset)))
  have hiff9 : (offset == BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) =
      fitsSigned 9 offset := by
    rw [h9w_eq]
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq]
    exact (fitsSigned_iff_signExtend 9 (by omega) (by omega) offset).symm
  by_cases h12 : (unsignedOffset && decide (offset = (BitVec.ofNat 64 ((offset >>> (1 : Nat)).toNat % 4096)) <<< (1 : Nat))) = true
  · have hoff : offset = (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> (1 : Nat)))) <<< (1 : Nat) := by
      have h := of_decide_eq_true (Bool.and_eq_true_iff.mp h12).2
      calc offset = (BitVec.ofNat 64 ((offset >>> (1 : Nat)).toNat % 4096)) <<< (1 : Nat) := h
        _ = (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> (1 : Nat)))) <<< (1 : Nat) := by
            congr 1
            exact imm12_eq 1 offset
    have hu : unsignedOffset = true := (Bool.and_eq_true_iff.mp h12).1
    have hw : encodeInsn32 (.loadStoreImmediate 1 true .store false unsignedOffset offset rn rt) =
        some (fields [(2, 1), (6, 57), (2, 0), (12, ((offset >>> (1 : Nat)).toNat % 4096)),
          (5, rn), (5, rt)]) := by
      simp only [encodeInsn32]
      split
      · simp
      · exact absurd h12 ‹_›
    rw [hu] at hw
    rw [hu, encodeBytes_eq_of_encodeInsn32 _ _ hw]
    simp only [arm8Encode, arm8Encode_loadStoreImm12_store16 offset (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rt) hoff,
      fields_loadStoreImm12, imm12Word_eq]
    rfl
  · have hfall : (unsignedOffset && (offset == (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> (1 : Nat)))) <<< (1 : Nat))) = false := by
      cases hu : unsignedOffset
      · rfl
      · have hp : decide (offset = (BitVec.ofNat 64 ((offset >>> (1 : Nat)).toNat % 4096)) <<< (1 : Nat)) = false := by
          have h := h12
          rw [hu] at h
          simpa using h
        simp only [hiff12, hp, Bool.true_and]
    by_cases h9 : fitsSigned 9 offset = true
    · have hsx : offset = BitVec.signExtend 64 (holWordExtract 9 8 0 offset) := by
        have h : (offset == BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) = true := by
          rw [hiff9]
          exact h9
        exact beq_iff_eq.mp h
      have hw : encodeInsn32 (.loadStoreImmediate 1 true .store false unsignedOffset offset rn rt) =
          some (fields [(2, 1), (6, 56), (2, 0), (1, 0), (9, offset.toNat % 512),
            (1, 0), (1, 0), (5, rn), (5, rt)]) := by
        simp only [encodeInsn32]
        split
        · exact absurd ‹_› h12
        · simp
      rw [encodeBytes_eq_of_encodeInsn32 _ _ hw]
      simp only [arm8Encode, arm8Encode_loadStoreImm9_store16 offset unsignedOffset (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rt)
        hfall hsx, fields_loadStoreImm9, imm9Word_eq]
    · have h9' : (offset == BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) = false := by
        rw [hiff9]
        simpa [Bool.not_eq_true] using h9
      have hg : ¬ (unsignedOffset = true ∧ offset = (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> (1 : Nat)))) <<< (1 : Nat)) := by
        intro h
        have h' : (unsignedOffset && (offset == (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> (1 : Nat)))) <<< (1 : Nat))) = true := by
          simp only [Bool.and_eq_true_iff, beq_iff_eq]
          exact ⟨h.1, h.2⟩
        rw [h'] at hfall
        exact absurd hfall (by decide)
      have hs : BitVec.setWidth 2 (BitVec.ofNat 16 1) = BitVec.ofNat 2 1 := by decide
      have h3 : (BitVec.ofNat 2 1).toNat = 1 := by decide
      have hload : (MemOp.MemOp_STORE == MemOp.MemOp_STORE) = true := by decide
      have hnrm : (AccType.AccType_NORMAL == AccType.AccType_NORMAL) = true := by decide
      have hpref : (MemOp.MemOp_STORE == MemOp.MemOp_PREFETCH) = false := by decide
      have hstore : (MemOp.MemOp_STORE == MemOp.MemOp_STORE) = true := by decide
      have hnf : ((!false : Bool) = true) := rfl
      have hw : encodeInsn32 (.loadStoreImmediate 1 true .store false unsignedOffset offset rn rt) =
          none := by
        simp only [encodeInsn32]
        split
        · exact absurd ‹_› h12
        · rfl
      rw [encodeBytes_eq_of_encodeInsn32_none _ hw]
      simp only [arm8Encode, Encode, e_load_store, e_LoadStoreImmediate, hs, h3, hload, hnrm,
        hpref, Bool.false_eq_true, if_false, hnf, if_true, Bool.and_true,
        Bool.and_eq_true_iff, beq_iff_eq, hg, h9']

/-- A 8-bit load encodes to the same four bytes on both sides. -/
theorem encodeBytes_loadStore8_load (unsignedOffset : Bool) (offset : BitVec 64) (rn rt : Nat) :
    encodeBytes (.loadStoreImmediate 0 false .load false unsignedOffset offset rn rt) =
      arm8Encode (.LoadStore (.«LoadStoreImmediate@8»
        ((BitVec.ofNat 8 0), false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
         false, unsignedOffset, offset, BitVec.ofNat 5 rn, BitVec.ofNat 5 rt))) := by
  have hiff12 : (offset == (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> (0 : Nat)))) <<< (0 : Nat)) =
      decide (offset = (BitVec.ofNat 64 ((offset >>> (0 : Nat)).toNat % 4096)) <<< (0 : Nat)) := by
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq, decide_eq_true_eq]
    exact Iff.intro
      (fun h => h.trans (congrArg (fun x : BitVec 64 => x <<< (0 : Nat)) (imm12_eq 0 offset).symm))
      (fun h => h.trans (congrArg (fun x : BitVec 64 => x <<< (0 : Nat)) (imm12_eq 0 offset)))
  have hiff9 : (offset == BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) =
      fitsSigned 9 offset := by
    rw [h9w_eq]
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq]
    exact (fitsSigned_iff_signExtend 9 (by omega) (by omega) offset).symm
  by_cases h12 : (unsignedOffset && decide (offset = (BitVec.ofNat 64 ((offset >>> (0 : Nat)).toNat % 4096)) <<< (0 : Nat))) = true
  · have hoff : offset = (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> (0 : Nat)))) <<< (0 : Nat) := by
      have h := of_decide_eq_true (Bool.and_eq_true_iff.mp h12).2
      calc offset = (BitVec.ofNat 64 ((offset >>> (0 : Nat)).toNat % 4096)) <<< (0 : Nat) := h
        _ = (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> (0 : Nat)))) <<< (0 : Nat) := by
            congr 1
            exact imm12_eq 0 offset
    have hu : unsignedOffset = true := (Bool.and_eq_true_iff.mp h12).1
    have hw : encodeInsn32 (.loadStoreImmediate 0 false .load false unsignedOffset offset rn rt) =
        some (fields [(2, 0), (6, 57), (2, 1), (12, ((offset >>> (0 : Nat)).toNat % 4096)),
          (5, rn), (5, rt)]) := by
      simp only [encodeInsn32]
      split
      · simp
      · exact absurd h12 ‹_›
    rw [hu] at hw
    rw [hu, encodeBytes_eq_of_encodeInsn32 _ _ hw]
    simp only [arm8Encode, arm8Encode_loadStoreImm12_load8 offset (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rt) hoff,
      fields_loadStoreImm12, imm12Word_eq]
    rfl
  · have hfall : (unsignedOffset && (offset == (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> (0 : Nat)))) <<< (0 : Nat))) = false := by
      cases hu : unsignedOffset
      · rfl
      · have hp : decide (offset = (BitVec.ofNat 64 ((offset >>> (0 : Nat)).toNat % 4096)) <<< (0 : Nat)) = false := by
          have h := h12
          rw [hu] at h
          simpa using h
        simp only [hiff12, hp, Bool.true_and]
    by_cases h9 : fitsSigned 9 offset = true
    · have hsx : offset = BitVec.signExtend 64 (holWordExtract 9 8 0 offset) := by
        have h : (offset == BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) = true := by
          rw [hiff9]
          exact h9
        exact beq_iff_eq.mp h
      have hw : encodeInsn32 (.loadStoreImmediate 0 false .load false unsignedOffset offset rn rt) =
          some (fields [(2, 0), (6, 56), (2, 1), (1, 0), (9, offset.toNat % 512),
            (1, 0), (1, 0), (5, rn), (5, rt)]) := by
        simp only [encodeInsn32]
        split
        · exact absurd ‹_› h12
        · simp
      rw [encodeBytes_eq_of_encodeInsn32 _ _ hw]
      simp only [arm8Encode, arm8Encode_loadStoreImm9_load8 offset unsignedOffset (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rt)
        hfall hsx, fields_loadStoreImm9, imm9Word_eq]
    · have h9' : (offset == BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) = false := by
        rw [hiff9]
        simpa [Bool.not_eq_true] using h9
      have hg : ¬ (unsignedOffset = true ∧ offset = (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> (0 : Nat)))) <<< (0 : Nat)) := by
        intro h
        have h' : (unsignedOffset && (offset == (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> (0 : Nat)))) <<< (0 : Nat))) = true := by
          simp only [Bool.and_eq_true_iff, beq_iff_eq]
          exact ⟨h.1, h.2⟩
        rw [h'] at hfall
        exact absurd hfall (by decide)
      have hs : BitVec.setWidth 2 (BitVec.ofNat 8 0) = BitVec.ofNat 2 0 := by decide
      have h3 : (BitVec.ofNat 2 0).toNat = 0 := by decide
      have hload : (MemOp.MemOp_LOAD == MemOp.MemOp_LOAD) = true := by decide
      have hnrm : (AccType.AccType_NORMAL == AccType.AccType_NORMAL) = true := by decide
      have hpref : (MemOp.MemOp_LOAD == MemOp.MemOp_PREFETCH) = false := by decide
      have hstore : (MemOp.MemOp_LOAD == MemOp.MemOp_STORE) = false := by decide
      have hnf : ((!false : Bool) = true) := rfl
      have hw : encodeInsn32 (.loadStoreImmediate 0 false .load false unsignedOffset offset rn rt) =
          none := by
        simp only [encodeInsn32]
        split
        · exact absurd ‹_› h12
        · rfl
      rw [encodeBytes_eq_of_encodeInsn32_none _ hw]
      simp only [arm8Encode, Encode, e_load_store, e_LoadStoreImmediate, hs, h3, hload, hnrm,
        hpref, Bool.false_eq_true, if_false, hnf, if_true, Bool.and_true,
        Bool.and_eq_true_iff, beq_iff_eq, hg, h9']

/-- A 8-bit store encodes to the same four bytes on both sides. -/
theorem encodeBytes_loadStore8_store (unsignedOffset : Bool) (offset : BitVec 64) (rn rt : Nat) :
    encodeBytes (.loadStoreImmediate 0 false .store false unsignedOffset offset rn rt) =
      arm8Encode (.LoadStore (.«LoadStoreImmediate@8»
        ((BitVec.ofNat 8 0), false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
         false, unsignedOffset, offset, BitVec.ofNat 5 rn, BitVec.ofNat 5 rt))) := by
  have hiff12 : (offset == (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> (0 : Nat)))) <<< (0 : Nat)) =
      decide (offset = (BitVec.ofNat 64 ((offset >>> (0 : Nat)).toNat % 4096)) <<< (0 : Nat)) := by
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq, decide_eq_true_eq]
    exact Iff.intro
      (fun h => h.trans (congrArg (fun x : BitVec 64 => x <<< (0 : Nat)) (imm12_eq 0 offset).symm))
      (fun h => h.trans (congrArg (fun x : BitVec 64 => x <<< (0 : Nat)) (imm12_eq 0 offset)))
  have hiff9 : (offset == BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) =
      fitsSigned 9 offset := by
    rw [h9w_eq]
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq]
    exact (fitsSigned_iff_signExtend 9 (by omega) (by omega) offset).symm
  by_cases h12 : (unsignedOffset && decide (offset = (BitVec.ofNat 64 ((offset >>> (0 : Nat)).toNat % 4096)) <<< (0 : Nat))) = true
  · have hoff : offset = (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> (0 : Nat)))) <<< (0 : Nat) := by
      have h := of_decide_eq_true (Bool.and_eq_true_iff.mp h12).2
      calc offset = (BitVec.ofNat 64 ((offset >>> (0 : Nat)).toNat % 4096)) <<< (0 : Nat) := h
        _ = (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> (0 : Nat)))) <<< (0 : Nat) := by
            congr 1
            exact imm12_eq 0 offset
    have hu : unsignedOffset = true := (Bool.and_eq_true_iff.mp h12).1
    have hw : encodeInsn32 (.loadStoreImmediate 0 false .store false unsignedOffset offset rn rt) =
        some (fields [(2, 0), (6, 57), (2, 0), (12, ((offset >>> (0 : Nat)).toNat % 4096)),
          (5, rn), (5, rt)]) := by
      simp only [encodeInsn32]
      split
      · simp
      · exact absurd h12 ‹_›
    rw [hu] at hw
    rw [hu, encodeBytes_eq_of_encodeInsn32 _ _ hw]
    simp only [arm8Encode, arm8Encode_loadStoreImm12_store8 offset (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rt) hoff,
      fields_loadStoreImm12, imm12Word_eq]
    rfl
  · have hfall : (unsignedOffset && (offset == (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> (0 : Nat)))) <<< (0 : Nat))) = false := by
      cases hu : unsignedOffset
      · rfl
      · have hp : decide (offset = (BitVec.ofNat 64 ((offset >>> (0 : Nat)).toNat % 4096)) <<< (0 : Nat)) = false := by
          have h := h12
          rw [hu] at h
          simpa using h
        simp only [hiff12, hp, Bool.true_and]
    by_cases h9 : fitsSigned 9 offset = true
    · have hsx : offset = BitVec.signExtend 64 (holWordExtract 9 8 0 offset) := by
        have h : (offset == BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) = true := by
          rw [hiff9]
          exact h9
        exact beq_iff_eq.mp h
      have hw : encodeInsn32 (.loadStoreImmediate 0 false .store false unsignedOffset offset rn rt) =
          some (fields [(2, 0), (6, 56), (2, 0), (1, 0), (9, offset.toNat % 512),
            (1, 0), (1, 0), (5, rn), (5, rt)]) := by
        simp only [encodeInsn32]
        split
        · exact absurd ‹_› h12
        · simp
      rw [encodeBytes_eq_of_encodeInsn32 _ _ hw]
      simp only [arm8Encode, arm8Encode_loadStoreImm9_store8 offset unsignedOffset (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rt)
        hfall hsx, fields_loadStoreImm9, imm9Word_eq]
    · have h9' : (offset == BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) = false := by
        rw [hiff9]
        simpa [Bool.not_eq_true] using h9
      have hg : ¬ (unsignedOffset = true ∧ offset = (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> (0 : Nat)))) <<< (0 : Nat)) := by
        intro h
        have h' : (unsignedOffset && (offset == (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> (0 : Nat)))) <<< (0 : Nat))) = true := by
          simp only [Bool.and_eq_true_iff, beq_iff_eq]
          exact ⟨h.1, h.2⟩
        rw [h'] at hfall
        exact absurd hfall (by decide)
      have hs : BitVec.setWidth 2 (BitVec.ofNat 8 0) = BitVec.ofNat 2 0 := by decide
      have h3 : (BitVec.ofNat 2 0).toNat = 0 := by decide
      have hload : (MemOp.MemOp_STORE == MemOp.MemOp_STORE) = true := by decide
      have hnrm : (AccType.AccType_NORMAL == AccType.AccType_NORMAL) = true := by decide
      have hpref : (MemOp.MemOp_STORE == MemOp.MemOp_PREFETCH) = false := by decide
      have hstore : (MemOp.MemOp_STORE == MemOp.MemOp_STORE) = true := by decide
      have hnf : ((!false : Bool) = true) := rfl
      have hw : encodeInsn32 (.loadStoreImmediate 0 false .store false unsignedOffset offset rn rt) =
          none := by
        simp only [encodeInsn32]
        split
        · exact absurd ‹_› h12
        · rfl
      rw [encodeBytes_eq_of_encodeInsn32_none _ hw]
      simp only [arm8Encode, Encode, e_load_store, e_LoadStoreImmediate, hs, h3, hload, hnrm,
        hpref, Bool.false_eq_true, if_false, hnf, if_true, Bool.and_true,
        Bool.and_eq_true_iff, beq_iff_eq, hg, h9']

end Flapjack.Compiler.Encoders.Arm8.L3
