module

public import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Mem
public import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Skip
public import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Const
public import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Arith
public import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.LogicalShiftedRegister
public import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.LogicalImmediateBinop
public import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.AddSubImmediate
public import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Shift
public import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.ShiftImmediate
public import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.ShiftBitfieldCase
public import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Division
public import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.LongMul
public import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.LongDiv
public import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.AddCarry
public import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Overflow
public import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Loc
public import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.LocBig
public import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Branch
public import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.JumpCmp
public import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Call
public import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.JumpReg
public import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Fp

-- Sum `==` must reduce by `rfl`/`decide`; core's derived instance is not exposed.
import all Init.Data.Sum.Basic
@[expose] public section

/-! # `encoder_correct arm8TargetL3`

The ARMv8 target over the L3 model satisfies CakeML's `encoder_correct`
(`asmPropsScript.sml`): `target_ok` and the simulation of every asm instruction
the ARMv8 lowering can emit, under every projection-preserving interference
environment.  This is the obligation `mc_conf_ok` asks of a machine
configuration, so it is what instantiates the Pancake-to-target theorem at the
L3 ARMv8 model.

This module is the port of HOL's `arm8_encoder_correct`
(`cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml`):
`arm8EncoderCorrectL3` carries that tag and is `reviewed_exact`, and the proof
dispatches each `HolInst` constructor to its tagged case theorem.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
  Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.Arm8.L3.Target

/-! ## Offset-branch helpers -/

/-- A `BEq` inequality as a boolean equality. -/
private theorem arm8EqFalseOfNe (a b : BitVec 64) (h : ¬(a = b)) : (a == b) = false := by
  cases hb : (a == b) with
  | false => rfl
  | true => exact absurd (beq_iff_eq.mp hb) h

/-- `arm8_ast`'s scaled-branch test is false once the offset is not the scaled
form and its sign bit is clear. -/
private theorem arm8AndFalseOfNe (off X : BitVec 64) (hmsb : off.msb = false)
    (h : ¬(off = X)) : ((!off.msb) && (off == X)) = false := by
  rw [arm8EqFalseOfNe off X h, hmsb]
  rfl

/-- The zero-shift scaled form: `arm8_ast`'s twelve-bit extract of an unscaled
offset. -/
private theorem arm8ScaledFormZero (off : BitVec 64) :
    BitVec.zeroExtend 64 (BitVec.ofNat 12 off.toNat) =
      BitVec.setWidth 64 (holWordExtract 12 11 0 off) := by
  simpa using arm8ScaledForm_eq off 0

/-- A byte offset inside `[0, 4095]` is already its zero-shift scaled form. -/
private theorem arm8ByteScaledForm (off : BitVec 64) (hmsb : off.msb = false)
    (hhi : off.toInt ≤ 4095) :
    off = (BitVec.setWidth 64 (holWordExtract 12 11 0 off)) <<< 0 := by
  have hcond := BitVec.toInt_eq_msb_cond off
  rw [hmsb] at hcond
  simp only [Bool.false_eq_true, ite_false] at hcond
  have hsmall : off.toNat < 4096 := by omega
  rw [← arm8ScaledFormZero off]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- A negative byte offset is its own signed nine-bit form. -/
private theorem arm8NineBitForm_of_byte (off : BitVec 64) (hmsb : off.msb = true)
    (hlo : (-256 : Int) ≤ off.toInt) :
    off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat) :=
  arm8NineBitForm_of_range off hlo (by
    have := BitVec.toInt_neg_of_msb_true hmsb
    omega)

/-- The configured `byte_offset_ok` window. -/
private theorem arm8ByteOffsetBounds (off : BitVec 64)
    (hok : asmByteOffsetOkExact arm8ConfigL3 off = true) :
    (-256 : Int) ≤ off.toInt ∧ off.toInt ≤ 4095 := by
  simp only [asmByteOffsetOkExact, arm8ConfigL3, asmOffsetOkExact, Bool.and_eq_true] at hok
  obtain ⟨⟨hlo, hhi⟩, -⟩ := hok
  exact ⟨arm8DecideOfTrue _ hlo, arm8DecideOfTrue _ hhi⟩

/-- The configured `hw_offset_ok` window. -/
private theorem arm8HwOffsetBounds (off : BitVec 64)
    (hok : asmHwOffsetOkExact arm8ConfigL3 off = true) :
    (-4351 : Int) ≤ off.toInt ∧ off.toInt ≤ 4350 := by
  simp only [asmHwOffsetOkExact, arm8ConfigL3, asmOffsetOkExact, Bool.and_eq_true] at hok
  obtain ⟨⟨hlo, hhi⟩, -⟩ := hok
  exact ⟨arm8DecideOfTrue _ hlo, arm8DecideOfTrue _ hhi⟩

/-- The far-branch immediate of a negative offset is 12-bit encodable, from the
offset's window. -/
private theorem arm8FarLowNegOfBounds (off : BitVec 64)
    (hlo : (-4351 : Int) ≤ off.toInt) (hhi : off.toInt ≤ 4350)
    (hnsx : ¬(off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)))
    (hmsb : off.msb = true) :
    (-off - (0x100 : BitVec 64)) &&& ~~~(4095 : BitVec 64) = (0 : BitVec 64) := by
  have h := arm8FarImm_encodable_of_bounds off hlo hhi hnsx
  simpa [hmsb] using h

/-- The far-branch immediate of a positive offset is 12-bit encodable, from the
offset's window. -/
private theorem arm8FarLowPosOfBounds (off : BitVec 64)
    (hlo : (-4351 : Int) ≤ off.toInt) (hhi : off.toInt ≤ 4350)
    (hnsx : ¬(off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)))
    (hmsbf : off.msb = false) :
    (off - (0xFF : BitVec 64)) &&& ~~~(4095 : BitVec 64) = (0 : BitVec 64) := by
  have h := arm8FarImm_encodable_of_bounds off hlo hhi hnsx
  simpa [hmsbf] using h

/-- The far-branch immediate of a negative offset, from `addr_offset_ok`. -/
private theorem arm8FarLowNeg (off : BitVec 64)
    (hok : asmAddrOffsetOkExact arm8ConfigL3 off = true)
    (hnsx : ¬(off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)))
    (hmsb : off.msb = true) :
    (-off - (0x100 : BitVec 64)) &&& ~~~(4095 : BitVec 64) = (0 : BitVec 64) := by
  obtain ⟨hlo, hhi⟩ := arm8FarOffsetBounds off hok
  exact arm8FarLowNegOfBounds off hlo hhi hnsx hmsb

/-- The far-branch immediate of a positive offset, from `addr_offset_ok`. -/
private theorem arm8FarLowPos (off : BitVec 64)
    (hok : asmAddrOffsetOkExact arm8ConfigL3 off = true)
    (hnsx : ¬(off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)))
    (hmsbf : off.msb = false) :
    (off - (0xFF : BitVec 64)) &&& ~~~(4095 : BitVec 64) = (0 : BitVec 64) := by
  obtain ⟨hlo, hhi⟩ := arm8FarOffsetBounds off hok
  exact arm8FarLowPosOfBounds off hlo hhi hnsx hmsbf

/-! ## `Mem` offset-branch dispatch -/

/-- The `.mem .load` constructor: `imm9`, scaled or far-offset, split on the
offset's sign bit and scaled form. -/
theorem arm8MemLoadCase (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem .load dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms) :
    CaseGoal (.inst (.mem .load dest (.addr base off))) s1 s2 ms := by
  obtain ⟨hs, hr⟩ := h
  have hok : asmAddrOffsetOkExact arm8ConfigL3 off = true := by
    have h' := hs.2.2.2.2.2.2
    simp [asmOkExact, asmInstOkExact, Bool.and_eq_true] at h'
    exact h'.2
  by_cases hsx : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)
  · by_cases hmsb : off.msb = true
    · exact arm8_encoder_correct_mem_load_neg dest base off s1 s2 ms ⟨hs, hr⟩ hsx hmsb
    · have hmsbf : off.msb = false := by simpa using hmsb
      by_cases hscaled : off = (BitVec.setWidth 64 (holWordExtract 12 11 0 (off >>> 3))) <<< 3
      · exact arm8_encoder_correct_mem_load_scaled dest base off s1 s2 ms ⟨hs, hr⟩ hmsbf hscaled
      · exact arm8_encoder_correct_mem_load_pos_unscaled dest base off s1 s2 ms ⟨hs, hr⟩ hsx hmsbf
          (arm8EqFalseOfNe off _ hscaled)
  · by_cases hmsb : off.msb = true
    · exact arm8_encoder_correct_mem_load_far_neg dest base off s1 s2 ms ⟨hs, hr⟩ hsx hmsb
        (arm8FarLowNeg off hok hsx hmsb)
    · have hmsbf : off.msb = false := by simpa using hmsb
      by_cases hscaled : off = (BitVec.setWidth 64 (holWordExtract 12 11 0 (off >>> 3))) <<< 3
      · exact arm8_encoder_correct_mem_load_scaled dest base off s1 s2 ms ⟨hs, hr⟩ hmsbf hscaled
      · have hscaled_ne :
            ¬(off = (BitVec.zeroExtend 64 (BitVec.ofNat 12 (off >>> 3).toNat)) <<< 3) := by
          intro hh
          rw [arm8ScaledForm_eq off 3] at hh
          exact hscaled hh
        exact arm8_encoder_correct_mem_load_far_pos dest base off s1 s2 ms ⟨hs, hr⟩ hsx hmsbf
          hscaled_ne (arm8FarLowPos off hok hsx hmsbf)

/-- The `.mem .store` constructor: the `imm9` theorem absorbs the sign-bit
distinction through its fall condition. -/
theorem arm8MemStoreCase (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem .store dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms) :
    CaseGoal (.inst (.mem .store dest (.addr base off))) s1 s2 ms := by
  obtain ⟨hs, hr⟩ := h
  have hok : asmAddrOffsetOkExact arm8ConfigL3 off = true := by
    have h' := hs.2.2.2.2.2.2
    simp [asmOkExact, asmInstOkExact, Bool.and_eq_true] at h'
    exact h'.2
  by_cases hsx : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)
  · by_cases hmsb : off.msb = true
    · exact arm8_encoder_correct_mem_store_imm9 dest base off s1 s2 ms ⟨hs, hr⟩ hsx
        (by simp [hmsb])
    · have hmsbf : off.msb = false := by simpa using hmsb
      by_cases hscaled : off = (BitVec.setWidth 64 (holWordExtract 12 11 0 (off >>> 3))) <<< 3
      · exact arm8_encoder_correct_mem_store_scaled dest base off s1 s2 ms ⟨hs, hr⟩ hmsbf hscaled
      · exact arm8_encoder_correct_mem_store_imm9 dest base off s1 s2 ms ⟨hs, hr⟩ hsx
          (arm8AndFalseOfNe off _ hmsbf hscaled)
  · by_cases hmsb : off.msb = true
    · exact arm8_encoder_correct_mem_store_far_neg dest base off s1 s2 ms ⟨hs, hr⟩ hsx hmsb
        (arm8FarLowNeg off hok hsx hmsb)
    · have hmsbf : off.msb = false := by simpa using hmsb
      by_cases hscaled : off = (BitVec.setWidth 64 (holWordExtract 12 11 0 (off >>> 3))) <<< 3
      · exact arm8_encoder_correct_mem_store_scaled dest base off s1 s2 ms ⟨hs, hr⟩ hmsbf hscaled
      · have hscaled_ne :
            ¬(off = (BitVec.zeroExtend 64 (BitVec.ofNat 12 (off >>> 3).toNat)) <<< 3) := by
          intro hh
          rw [arm8ScaledForm_eq off 3] at hh
          exact hscaled hh
        exact arm8_encoder_correct_mem_store_far_pos dest base off s1 s2 ms ⟨hs, hr⟩ hsx hmsbf
          hscaled_ne (arm8FarLowPos off hok hsx hmsbf)

/-- The `.mem .load16` constructor: `imm9`, scaled or far-offset. -/
theorem arm8MemLoad16Case (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem .load16 dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms) :
    CaseGoal (.inst (.mem .load16 dest (.addr base off))) s1 s2 ms := by
  obtain ⟨hs, hr⟩ := h
  have hok : asmHwOffsetOkExact arm8ConfigL3 off = true := by
    have h' := hs.2.2.2.2.2.2
    simp [asmOkExact, asmInstOkExact, Bool.and_eq_true] at h'
    exact h'.2.1
  obtain ⟨hlo, hhi⟩ := arm8HwOffsetBounds off hok
  by_cases hsx : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)
  · by_cases hmsb : off.msb = true
    · exact arm8_encoder_correct_mem_load16_imm9 dest base off s1 s2 ms ⟨hs, hr⟩ hsx (by simp [hmsb])
    · have hmsbf : off.msb = false := by simpa using hmsb
      by_cases hscaled : off = (BitVec.setWidth 64 (holWordExtract 12 11 0 (off >>> 1))) <<< 1
      · exact arm8_encoder_correct_mem_load16_scaled dest base off s1 s2 ms ⟨hs, hr⟩ hmsbf hscaled
      · exact arm8_encoder_correct_mem_load16_imm9 dest base off s1 s2 ms ⟨hs, hr⟩ hsx
          (arm8AndFalseOfNe off _ hmsbf hscaled)
  · by_cases hmsb : off.msb = true
    · exact arm8_encoder_correct_mem_load16_far_neg dest base off s1 s2 ms ⟨hs, hr⟩ hsx hmsb
        (arm8FarLowNegOfBounds off hlo hhi hsx hmsb)
    · have hmsbf : off.msb = false := by simpa using hmsb
      by_cases hscaled : off = (BitVec.setWidth 64 (holWordExtract 12 11 0 (off >>> 1))) <<< 1
      · exact arm8_encoder_correct_mem_load16_scaled dest base off s1 s2 ms ⟨hs, hr⟩ hmsbf hscaled
      · have hscaled_ne : ¬(off = (BitVec.zeroExtend 64 (BitVec.ofNat 12 (off >>> 1).toNat)) <<< 1) := by
          intro hh
          rw [arm8ScaledForm_eq off 1] at hh
          exact hscaled hh
        exact arm8_encoder_correct_mem_load16_far_pos dest base off s1 s2 ms ⟨hs, hr⟩ hsx hmsbf hscaled_ne
          (arm8FarLowPosOfBounds off hlo hhi hsx hmsbf)

/-- The `.mem .store16` constructor: `imm9`, scaled or far-offset. -/
theorem arm8MemStore16Case (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem .store16 dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms) :
    CaseGoal (.inst (.mem .store16 dest (.addr base off))) s1 s2 ms := by
  obtain ⟨hs, hr⟩ := h
  have hok : asmHwOffsetOkExact arm8ConfigL3 off = true := by
    have h' := hs.2.2.2.2.2.2
    simp [asmOkExact, asmInstOkExact, Bool.and_eq_true] at h'
    exact h'.2.1
  obtain ⟨hlo, hhi⟩ := arm8HwOffsetBounds off hok
  by_cases hsx : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)
  · by_cases hmsb : off.msb = true
    · exact arm8_encoder_correct_mem_store16_imm9 dest base off s1 s2 ms ⟨hs, hr⟩ hsx (by simp [hmsb])
    · have hmsbf : off.msb = false := by simpa using hmsb
      by_cases hscaled : off = (BitVec.setWidth 64 (holWordExtract 12 11 0 (off >>> 1))) <<< 1
      · exact arm8_encoder_correct_mem_store16_scaled dest base off s1 s2 ms ⟨hs, hr⟩ hmsbf hscaled
      · exact arm8_encoder_correct_mem_store16_imm9 dest base off s1 s2 ms ⟨hs, hr⟩ hsx
          (arm8AndFalseOfNe off _ hmsbf hscaled)
  · by_cases hmsb : off.msb = true
    · exact arm8_encoder_correct_mem_store16_far_neg dest base off s1 s2 ms ⟨hs, hr⟩ hsx hmsb
        (arm8FarLowNegOfBounds off hlo hhi hsx hmsb)
    · have hmsbf : off.msb = false := by simpa using hmsb
      by_cases hscaled : off = (BitVec.setWidth 64 (holWordExtract 12 11 0 (off >>> 1))) <<< 1
      · exact arm8_encoder_correct_mem_store16_scaled dest base off s1 s2 ms ⟨hs, hr⟩ hmsbf hscaled
      · have hscaled_ne : ¬(off = (BitVec.zeroExtend 64 (BitVec.ofNat 12 (off >>> 1).toNat)) <<< 1) := by
          intro hh
          rw [arm8ScaledForm_eq off 1] at hh
          exact hscaled hh
        exact arm8_encoder_correct_mem_store16_far_pos dest base off s1 s2 ms ⟨hs, hr⟩ hsx hmsbf hscaled_ne
          (arm8FarLowPosOfBounds off hlo hhi hsx hmsbf)

/-- The `.mem .load32` constructor: `imm9`, scaled or far-offset. -/
theorem arm8MemLoad32Case (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem .load32 dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms) :
    CaseGoal (.inst (.mem .load32 dest (.addr base off))) s1 s2 ms := by
  obtain ⟨hs, hr⟩ := h
  have hok : asmAddrOffsetOkExact arm8ConfigL3 off = true := by
    have h' := hs.2.2.2.2.2.2
    simp [asmOkExact, asmInstOkExact, Bool.and_eq_true] at h'
    exact h'.2
  obtain ⟨hlo, hhi⟩ := arm8FarOffsetBounds off hok
  by_cases hsx : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)
  · by_cases hmsb : off.msb = true
    · exact arm8_encoder_correct_mem_load32_imm9 dest base off s1 s2 ms ⟨hs, hr⟩ hsx (by simp [hmsb])
    · have hmsbf : off.msb = false := by simpa using hmsb
      by_cases hscaled : off = (BitVec.setWidth 64 (holWordExtract 12 11 0 (off >>> 2))) <<< 2
      · exact arm8_encoder_correct_mem_load32_scaled dest base off s1 s2 ms ⟨hs, hr⟩ hmsbf hscaled
      · exact arm8_encoder_correct_mem_load32_imm9 dest base off s1 s2 ms ⟨hs, hr⟩ hsx
          (arm8AndFalseOfNe off _ hmsbf hscaled)
  · by_cases hmsb : off.msb = true
    · exact arm8_encoder_correct_mem_load32_far_neg dest base off s1 s2 ms ⟨hs, hr⟩ hsx hmsb
        (arm8FarLowNegOfBounds off hlo hhi hsx hmsb)
    · have hmsbf : off.msb = false := by simpa using hmsb
      by_cases hscaled : off = (BitVec.setWidth 64 (holWordExtract 12 11 0 (off >>> 2))) <<< 2
      · exact arm8_encoder_correct_mem_load32_scaled dest base off s1 s2 ms ⟨hs, hr⟩ hmsbf hscaled
      · have hscaled_ne : ¬(off = (BitVec.zeroExtend 64 (BitVec.ofNat 12 (off >>> 2).toNat)) <<< 2) := by
          intro hh
          rw [arm8ScaledForm_eq off 2] at hh
          exact hscaled hh
        exact arm8_encoder_correct_mem_load32_far_pos dest base off s1 s2 ms ⟨hs, hr⟩ hsx hmsbf hscaled_ne
          (arm8FarLowPosOfBounds off hlo hhi hsx hmsbf)

/-- The `.mem .store32` constructor: `imm9`, scaled or far-offset. -/
theorem arm8MemStore32Case (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem .store32 dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms) :
    CaseGoal (.inst (.mem .store32 dest (.addr base off))) s1 s2 ms := by
  obtain ⟨hs, hr⟩ := h
  have hok : asmAddrOffsetOkExact arm8ConfigL3 off = true := by
    have h' := hs.2.2.2.2.2.2
    simp [asmOkExact, asmInstOkExact, Bool.and_eq_true] at h'
    exact h'.2
  obtain ⟨hlo, hhi⟩ := arm8FarOffsetBounds off hok
  by_cases hsx : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)
  · by_cases hmsb : off.msb = true
    · exact arm8_encoder_correct_mem_store32_imm9 dest base off s1 s2 ms ⟨hs, hr⟩ hsx (by simp [hmsb])
    · have hmsbf : off.msb = false := by simpa using hmsb
      by_cases hscaled : off = (BitVec.setWidth 64 (holWordExtract 12 11 0 (off >>> 2))) <<< 2
      · exact arm8_encoder_correct_mem_store32_scaled dest base off s1 s2 ms ⟨hs, hr⟩ hmsbf hscaled
      · exact arm8_encoder_correct_mem_store32_imm9 dest base off s1 s2 ms ⟨hs, hr⟩ hsx
          (arm8AndFalseOfNe off _ hmsbf hscaled)
  · by_cases hmsb : off.msb = true
    · exact arm8_encoder_correct_mem_store32_far_neg dest base off s1 s2 ms ⟨hs, hr⟩ hsx hmsb
        (arm8FarLowNegOfBounds off hlo hhi hsx hmsb)
    · have hmsbf : off.msb = false := by simpa using hmsb
      by_cases hscaled : off = (BitVec.setWidth 64 (holWordExtract 12 11 0 (off >>> 2))) <<< 2
      · exact arm8_encoder_correct_mem_store32_scaled dest base off s1 s2 ms ⟨hs, hr⟩ hmsbf hscaled
      · have hscaled_ne : ¬(off = (BitVec.zeroExtend 64 (BitVec.ofNat 12 (off >>> 2).toNat)) <<< 2) := by
          intro hh
          rw [arm8ScaledForm_eq off 2] at hh
          exact hscaled hh
        exact arm8_encoder_correct_mem_store32_far_pos dest base off s1 s2 ms ⟨hs, hr⟩ hsx hmsbf hscaled_ne
          (arm8FarLowPosOfBounds off hlo hhi hsx hmsbf)

/-- The `.mem .load8` constructor: the byte-offset window makes the far branch
unreachable — a negative offset is its own `imm9` form, a non-negative one is
its zero-shift scaled form. -/
theorem arm8MemLoad8Case (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem .load8 dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms) :
    CaseGoal (.inst (.mem .load8 dest (.addr base off))) s1 s2 ms := by
  obtain ⟨hs, hr⟩ := h
  have hok : asmByteOffsetOkExact arm8ConfigL3 off = true := by
    have h' := hs.2.2.2.2.2.2
    simp [asmOkExact, asmInstOkExact, Bool.and_eq_true] at h'
    exact h'.2
  obtain ⟨hlo, hhi⟩ := arm8ByteOffsetBounds off hok
  by_cases hsx : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)
  · by_cases hmsb : off.msb = true
    · exact arm8_encoder_correct_mem_load8_imm9 dest base off s1 s2 ms ⟨hs, hr⟩ hsx (by simp [hmsb])
    · have hmsbf : off.msb = false := by simpa using hmsb
      by_cases hscaled : off = (BitVec.setWidth 64 (holWordExtract 12 11 0 off)) <<< 0
      · exact arm8_encoder_correct_mem_load8_scaled dest base off s1 s2 ms ⟨hs, hr⟩ hmsbf hscaled
      · exact arm8_encoder_correct_mem_load8_imm9 dest base off s1 s2 ms ⟨hs, hr⟩ hsx
          (arm8AndFalseOfNe off _ hmsbf hscaled)
  · by_cases hmsb : off.msb = true
    · exact absurd (arm8NineBitForm_of_byte off hmsb hlo) hsx
    · have hmsbf : off.msb = false := by simpa using hmsb
      exact arm8_encoder_correct_mem_load8_scaled dest base off s1 s2 ms ⟨hs, hr⟩ hmsbf
        (arm8ByteScaledForm off hmsbf hhi)

/-- The `.mem .store8` constructor: the byte-offset window makes the far branch
unreachable — a negative offset is its own `imm9` form, a non-negative one is
its zero-shift scaled form. -/
theorem arm8MemStore8Case (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem .store8 dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms) :
    CaseGoal (.inst (.mem .store8 dest (.addr base off))) s1 s2 ms := by
  obtain ⟨hs, hr⟩ := h
  have hok : asmByteOffsetOkExact arm8ConfigL3 off = true := by
    have h' := hs.2.2.2.2.2.2
    simp [asmOkExact, asmInstOkExact, Bool.and_eq_true] at h'
    exact h'.2
  obtain ⟨hlo, hhi⟩ := arm8ByteOffsetBounds off hok
  by_cases hsx : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)
  · by_cases hmsb : off.msb = true
    · exact arm8_encoder_correct_mem_store8_imm9 dest base off s1 s2 ms ⟨hs, hr⟩ hsx (by simp [hmsb])
    · have hmsbf : off.msb = false := by simpa using hmsb
      by_cases hscaled : off = (BitVec.setWidth 64 (holWordExtract 12 11 0 off)) <<< 0
      · exact arm8_encoder_correct_mem_store8_scaled dest base off s1 s2 ms ⟨hs, hr⟩ hmsbf hscaled
      · exact arm8_encoder_correct_mem_store8_imm9 dest base off s1 s2 ms ⟨hs, hr⟩ hsx
          (arm8AndFalseOfNe off _ hmsbf hscaled)
  · by_cases hmsb : off.msb = true
    · exact absurd (arm8NineBitForm_of_byte off hmsb hlo) hsx
    · have hmsbf : off.msb = false := by simpa using hmsb
      exact arm8_encoder_correct_mem_store8_scaled dest base off s1 s2 ms ⟨hs, hr⟩ hmsbf
        (arm8ByteScaledForm off hmsbf hhi)

/-- The `.mem` constructor: dispatch on the memory operation. -/
theorem arm8MemCase (op : HolMemop) (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem op dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms) :
    CaseGoal (.inst (.mem op dest (.addr base off))) s1 s2 ms := by
  cases op with
  | load => exact arm8MemLoadCase dest base off s1 s2 ms h
  | load8 => exact arm8MemLoad8Case dest base off s1 s2 ms h
  | load16 => exact arm8MemLoad16Case dest base off s1 s2 ms h
  | load32 => exact arm8MemLoad32Case dest base off s1 s2 ms h
  | store => exact arm8MemStoreCase dest base off s1 s2 ms h
  | store8 => exact arm8MemStore8Case dest base off s1 s2 ms h
  | store16 => exact arm8MemStore16Case dest base off s1 s2 ms h
  | store32 => exact arm8MemStore32Case dest base off s1 s2 ms h

/-! ## `arith` dispatch -/

/-- The immediate operand of an add/sub binop is in one of the two
`valid_immediate` windows. -/
private theorem arm8AddSubImmValid (bop : BinOp) (hbop : bop = .add ∨ bop = .sub)
    (v : BitVec 64)
    (hok : asmRegImmOkExact (.inl bop) (.imm v) arm8ConfigL3 = true) :
    v &&& ~~~(4095 : BitVec 64) = (0 : BitVec 64) ∨
      v &&& ~~~(16773120 : BitVec 64) = (0 : BitVec 64) := by
  rcases hbop with rfl | rfl
  · simp only [asmRegImmOkExact, arm8ConfigL3, arm8ValidImmediate, Bool.or_eq_true,
      Bool.and_eq_true, beq_iff_eq] at hok
    rcases hok with ⟨h1, -⟩ | h | h
    · exact absurd h1 (by decide)
    · exact Or.inl (of_decide_eq_true h)
    · exact Or.inr (of_decide_eq_true h)
  · simp only [asmRegImmOkExact, arm8ConfigL3, arm8ValidImmediate, Bool.or_eq_true,
      Bool.and_eq_true, beq_iff_eq] at hok
    rcases hok with ⟨h1, -⟩ | h | h
    · exact absurd h1 (by decide)
    · exact Or.inl (of_decide_eq_true h)
    · exact Or.inr (of_decide_eq_true h)

/-- The step's `asm_ok` supplies the immediate-operand check. -/
private theorem arm8RegImmOk_of_step (bop : BinOp) (dest src : Nat) (v : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1
      (.inst (.arith (.binop bop dest src (.imm v)))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms) :
    asmRegImmOkExact (.inl bop) (.imm v) arm8ConfigL3 = true := by
  have h' := h.1.2.2.2.2.2
  simp only [asmOkExact, asmInstOkExact, asmArithOkExact, Bool.and_eq_true] at h'
  exact h'.2.2

/-- The `.arith (.binop ...)` constructor. -/
theorem arm8BinopCase (bop : HolBinop) (dest src : Nat) (right : HolRegImm 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.arith (.binop bop dest src right))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms) :
    CaseGoal (.inst (.arith (.binop bop dest src right))) s1 s2 ms := by
  cases right with
  | reg r =>
    cases bop with
    | add => exact arm8_encoder_correct_binop_addsub_reg false .add rfl dest src r s1 s2 ms h
    | sub => exact arm8_encoder_correct_binop_addsub_reg true .sub rfl dest src r s1 s2 ms h
    | and =>
      exact arm8_encoder_correct_binop_logic_reg .and (Or.inl rfl) dest src r s1 s2 ms h
    | or =>
      exact arm8_encoder_correct_binop_logic_reg .or (Or.inr (Or.inl rfl)) dest src r s1 s2 ms h
    | xor =>
      exact arm8_encoder_correct_binop_logic_reg .xor (Or.inr (Or.inr rfl)) dest src r s1 s2 ms h
  | imm v =>
    cases bop with
    | add =>
      exact arm8_encoder_correct_binop_addsub_imm false .add rfl dest src v
        (arm8AddSubImmValid .add (Or.inl rfl) v (arm8RegImmOk_of_step .add dest src v s1 s2 ms h))
        s1 s2 ms h
    | sub =>
      exact arm8_encoder_correct_binop_addsub_imm true .sub rfl dest src v
        (arm8AddSubImmValid .sub (Or.inr rfl) v (arm8RegImmOk_of_step .sub dest src v s1 s2 ms h))
        s1 s2 ms h
    | and =>
      exact arm8_encoder_correct_binop_logic_imm .and (Or.inl rfl) dest src v s1 s2 ms h
    | or =>
      exact arm8_encoder_correct_binop_logic_imm .or (Or.inr rfl) dest src v s1 s2 ms h
    | xor =>
      by_cases hneg : v = -1
      · exact arm8_encoder_correct_binop_xor_neg dest src v hneg s1 s2 ms h
      · exact arm8_encoder_correct_binop_xor_imm dest src v hneg s1 s2 ms h

/-- The `.arith (.shift ...)` constructor. -/
theorem arm8ShiftCase (sh : Flapjack.Shift) (dest src : Nat) (right : HolRegImm 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.arith (.shift sh dest src right))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms) :
    CaseGoal (.inst (.arith (.shift sh dest src right))) s1 s2 ms := by
  cases right with
  | reg r => exact arm8_encoder_correct_shift_reg sh dest src r s1 s2 ms h
  | imm v =>
    cases sh with
    | lsl => exact arm8_encoder_correct_shift_lsl_imm dest src v s1 s2 ms h
    | lsr => exact arm8_encoder_correct_shift_lsr_imm dest src v s1 s2 ms h
    | asr => exact arm8_encoder_correct_shift_asr_imm dest src v s1 s2 ms h
    | ror => exact arm8_encoder_correct_shift_ror_imm dest src v s1 s2 ms h

/-- The `.arith` constructor: dispatch on the arithmetic operation. -/
theorem arm8ArithCase (a : HolArith 64) (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.arith a)) s2 ∧
      targetStateRel arm8TargetL3 s1 ms) :
    CaseGoal (.inst (.arith a)) s1 s2 ms := by
  cases a with
  | binop bop dest src right => exact arm8BinopCase bop dest src right s1 s2 ms h
  | shift sh dest src right => exact arm8ShiftCase sh dest src right s1 s2 ms h
  | div dest dividend divisor => exact arm8_encoder_correct_div dest dividend divisor s1 s2 ms h
  | longMul dl dr sl sr => exact arm8_encoder_correct_longMul dl dr sl sr s1 s2 ms h
  | longDiv dl dr sl sr q => exact arm8_encoder_correct_longDiv dl dr sl sr q s1 s2 ms h
  | addCarry d rc sl sr => exact arm8_encoder_correct_addCarry d rc sl sr s1 s2 ms h
  | addOverflow dest res sl sr =>
    exact arm8_encoder_correct_addOverflow dest res sl sr s1 s2 ms h
  | subOverflow dest res sl sr =>
    exact arm8_encoder_correct_subOverflow dest res sl sr s1 s2 ms h

/-! ## `encoder_correct arm8TargetL3` -/

/-- `encoder_correct` for the L3 ARMv8 target: `target_ok` and every source
instruction, every interference environment, both assertions.  This is the
obligation `mc_conf_ok` asks of a machine configuration, so it is what
instantiates the Pancake-to-target theorem at the L3 ARMv8 model.

This is the assembling theorem of HOL's `arm8_encoder_correct`: it states
`encoder_correct arm8_target` at the L3 rendering, with `target_ok` supplied
by `arm8TargetL3_targetOk` and every `HolInst` constructor dispatched to its
tagged case theorem.  It adds no hypothesis beyond HOL's statement. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8EncoderCorrectL3 : encoderCorrect arm8TargetL3 := by
  refine ⟨arm8TargetL3_targetOk, ?_⟩
  intro s1 i s2 ms h
  cases i with
  | inst v =>
    cases v with
    | skip => exact arm8_encoder_correct_skip s1 s2 ms h
    | const r c => exact arm8_encoder_correct_const r c s1 s2 ms h
    | arith a => exact arm8ArithCase a s1 s2 ms h
    | mem op dest address =>
      cases address with
      | addr base off => exact arm8MemCase op dest base off s1 s2 ms h
    | fp f => exact arm8_encoder_correct_fp f s1 s2 ms h
  | jump target => exact arm8_encoder_correct_jump target s1 s2 ms h
  | jumpCmp cmp r right target =>
    cases right with
    | reg u => exact arm8_encoder_correct_jumpCmp_reg cmp r u target s1 s2 ms h
    | imm v => exact arm8_encoder_correct_jumpCmp_imm cmp r v target s1 s2 ms h
  | call target => exact arm8_encoder_correct_call target s1 s2 ms h
  | jumpReg r => exact arm8_encoder_correct_jumpReg r s1 s2 ms h
  | loc r off =>
    by_cases hrange : arm8LocInRange off = true
    · exact arm8_encoder_correct_loc_small r off hrange s1 s2 ms h
    · have hfalse : arm8LocInRange off = false := by
        cases hb : arm8LocInRange off with
        | false => rfl
        | true => exact absurd hb hrange
      exact arm8_encoder_correct_loc_big r off hfalse s1 s2 ms h

end Flapjack.Compiler.Encoders.Arm8.L3
