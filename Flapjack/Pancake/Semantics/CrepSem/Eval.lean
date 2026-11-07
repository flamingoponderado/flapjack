module

public import Flapjack.Pancake.Semantics.CrepRuntimeTarget
public import Flapjack.Compiler.Encoders.Asm
public import Flapjack.Pancake.Semantics.PanSemStateEval
public import Flapjack.Pancake.WordLang
public import Flapjack.Pancake.Semantics.CrepSem.WordAlignment

@[expose] public section

/-!
# Pancake Crepe expression evaluation

This file encodes the HOL `crepSem$state` fields without the target-only
operation and FFI-context fields carried by Flapjack's executable runtime.
The adapter below supplies the operations derived from a positive-width word
type, and the source-shaped evaluator follows `crepSem$eval_def`.
-/

namespace Flapjack

open Compiler.Encoders.Asm

def crepHolEvalFfiContext [OfNat α 0] : PanValueFfiContext α where
  sharedDomain := fun _ => false
  byteAlign := id
  bigEndian := false
  wordToBytes := fun _ _ => []
  wordOfBytes := fun _ _ => 0
  wordToByte := fun _ => 0
  byteToWord := fun _ => 0
  valueToNat := fun _ => 0

/-- Add the executable-only fields needed by the production evaluator. Its
    word operations and byte accessors are fixed from the word width and HOL's
    `be`; the placeholder FFI codec is unused by expression evaluation. -/
def CrepHolState.toRuntime [NeZero width]
    (state : CrepHolState (RiscV.Word width) σ) :
    CrepRuntimeState (RiscV.Word width) σ :=
  { locals := state.locals
    globals := state.globals
    code := state.code
    memory := state.memory
    memaddrs := state.memaddrs
    shMemaddrs := state.shMemaddrs
    memoryModel := RiscV.panRiscVMemoryModelForEndian state.bigEndian
    bytesInWord := BitVec.ofNat width (width / 8)
    ffiContext := crepHolEvalFfiContext
    clock := state.clock
    bigEndian := state.bigEndian
    ffi := state.ffi
    baseAddress := state.baseAddress
    topAddress := state.topAddress }

/-- Production adapter: the exact HOL-shaped `setCrepHolGlobals` on the
    field-only state commutes with `CrepHolState.toRuntime`, so the executable
    `setCrepRuntimeGlobals` performs the same global update. -/
theorem setCrepHolGlobals_toRuntime [NeZero width]
    (key : BitVec 5) (value : PanWordLab (RiscV.Word width))
    (state : CrepHolState (RiscV.Word width) σ) :
    (setCrepHolGlobals key value state).toRuntime =
      setCrepRuntimeGlobals key value state.toRuntime := rfl

/-! HOL `byte_align_def` clears the low bits selected by
    `LOG2 (dimindex DIV 8)`. -/
def holByteAlignBitVec [NeZero width] (address : BitVec width) : BitVec width :=
  let alignment := 2 ^ Nat.log2 (width / 8)
  BitVec.ofNat width ((address.toNat / alignment) * alignment)

/-- For `width ≥ 8`, production RISC-V alignment with
    `bytesInWord = width / 8` is HOL's `byte_align`, including non-power-of-two
    byte counts such as width 24 (bead `flapjack-pxn.18.5.4.3.4`). HOL leaves
    `LOG2 (width / 8)` unspecified when `width < 8`, so this Flapjack-only
    bridge makes no claim there. -/
theorem panRiscVByteAlign_bytesInWord_eq_holByteAlignBitVec [NeZero width]
    (hwidth : 8 ≤ width) (address : BitVec width) :
    RiscV.panRiscVByteAlign (BitVec.ofNat width (width / 8)) address =
      holByteAlignBitVec address := by
  have hlt : width / 8 < 2 ^ width :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.lt_two_pow_self)
  have hbytes0 : width / 8 ≠ 0 := by omega
  simp [RiscV.panRiscVByteAlign, holByteAlignBitVec,
    Nat.mod_eq_of_lt hlt, hbytes0]

/-- Lean-level equality of two Lean definitions at every positive width:
    production RISC-V alignment with `bytesInWord = width / 8` equals the Lean
    `holByteAlignBitVec`.  Only for `width ≥ 8` does this mean HOL `byte_align`
    (`panRiscVByteAlign_bytesInWord_eq_holByteAlignBitVec`).  Below width 8,
    HOL's `LOG2 0` is unspecified; there both sides fall back to the address
    identity (`Nat.log2 0 = 0` and the zero-byte-count branch), a Flapjack
    convention with no HOL claim.  Flapjack-only, untagged. -/
theorem panRiscVByteAlign_bytesInWord_eq_holByteAlignBitVec_lean [NeZero width]
    (address : BitVec width) :
    RiscV.panRiscVByteAlign (BitVec.ofNat width (width / 8)) address =
      holByteAlignBitVec address := by
  have hlt : width / 8 < 2 ^ width :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.lt_two_pow_self)
  unfold RiscV.panRiscVByteAlign holByteAlignBitVec
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  split
  · rename_i h0
    rw [h0]
    apply BitVec.eq_of_toNat_eq
    simp
  · rfl

/-- BitVec form of HOL `set_byte_def`: retain the high slice, insert the
    low eight bits of the byte at its byte offset, and retain the low slice. -/
def holFiniteWordSetByteBitVec (width offset : Nat)
    (byte value : BitVec width) : BitVec width :=
  (((value >>> (offset + 8)) <<< (offset + 8)) |||
      ((BitVec.setWidth width (BitVec.extractLsb' 0 8 byte)) <<< offset)) |||
    BitVec.setWidth width (BitVec.extractLsb' 0 offset value)

/-- Flapjack BitVec encoding lemma, with no separate HOL declaration: it gives
    the Nat value of a zero-based low slice after widening it back to the
    carrier width. Keeping this normalization separate makes the later
    four-byte `word_of_bytes` proof reason about bounded Nat lanes. -/
private theorem setWidth_extractLsb_zero_toNat (width length : Nat)
    (value : BitVec width) (hlen : length ≤ width) :
    (BitVec.setWidth width (BitVec.extractLsb' 0 length value)).toNat =
      value.toNat % 2 ^ length := by
  simp only [BitVec.toNat_setWidth, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one]
  have hsmall : value.toNat % 2 ^ length < 2 ^ length :=
    Nat.mod_lt _ (Nat.two_pow_pos _)
  have hpow : 2 ^ length ≤ 2 ^ width :=
    Nat.pow_le_pow_right (by omega) hlen
  rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hsmall hpow)]

/-- Flapjack proof infrastructure for the BitVec encoding of HOL `set_byte`;
    HOL has no separate Nat equation for this helper. The lower slice, inserted
    byte, and preserved upper slice occupy disjoint bit ranges. -/
theorem holFiniteWordSetByteBitVec_toNat (width offset : Nat)
    (byte value : BitVec width) (hoffset : offset + 8 ≤ width) :
    (holFiniteWordSetByteBitVec width offset byte value).toNat =
      (value.toNat / 2 ^ (offset + 8)) * 2 ^ (offset + 8) +
        (byte.toNat % 2 ^ 8) * 2 ^ offset + value.toNat % 2 ^ offset := by
  have hlow : value.toNat % 2 ^ offset < 2 ^ offset :=
    Nat.mod_lt _ (Nat.two_pow_pos _)
  have hbyte : byte.toNat % 2 ^ 8 < 2 ^ 8 :=
    Nat.mod_lt _ (Nat.two_pow_pos _)
  have hmid : (byte.toNat % 2 ^ 8) * 2 ^ offset +
      value.toNat % 2 ^ offset < 2 ^ (offset + 8) := by
    have hpow : 2 ^ (offset + 8) = 256 * 2 ^ offset := by
      rw [Nat.pow_add, show (2 : Nat) ^ 8 = 256 by decide, Nat.mul_comm]
    have hbyteLe : byte.toNat % 2 ^ 8 ≤ 255 := by omega
    have hscaled := Nat.mul_le_mul_right (2 ^ offset) hbyteLe
    rw [hpow]
    omega
  have hhigh : (value.toNat / 2 ^ (offset + 8)) * 2 ^ (offset + 8) <
      2 ^ width := by
    have hdiv := Nat.div_mul_le_self value.toNat (2 ^ (offset + 8))
    have hpow : 2 ^ (offset + 8) ≤ 2 ^ width :=
      Nat.pow_le_pow_right (by omega) hoffset
    omega
  have hlane : (byte.toNat % 2 ^ 8) * 2 ^ offset < 2 ^ width := by
    have hbyteTimes : (byte.toNat % 2 ^ 8) * 2 ^ offset <
        2 ^ (offset + 8) := by
      have hscaled := Nat.mul_lt_mul_of_pos_right hbyte (Nat.two_pow_pos offset)
      have hpow : 2 ^ (offset + 8) = 256 * 2 ^ offset := by
        rw [Nat.pow_add, show (2 : Nat) ^ 8 = 256 by decide, Nat.mul_comm]
      rw [hpow]
      rw [show (2 : Nat) ^ 8 = 256 by decide] at hscaled
      omega
    exact Nat.lt_of_lt_of_le hbyteTimes
      (Nat.pow_le_pow_right (by omega) hoffset)
  have hLowNat :
      (BitVec.setWidth width (BitVec.extractLsb' 0 offset value)).toNat =
        value.toNat % 2 ^ offset :=
    setWidth_extractLsb_zero_toNat width offset value (by omega)
  have hByteNat :
      (BitVec.setWidth width (BitVec.extractLsb' 0 8 byte)).toNat =
        byte.toNat % 2 ^ 8 :=
    setWidth_extractLsb_zero_toNat width 8 byte (by omega)
  have hHighNat :
      ((value >>> (offset + 8)) <<< (offset + 8)).toNat =
        (value.toNat / 2 ^ (offset + 8)) * 2 ^ (offset + 8) := by
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
      Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt hhigh]
  have hLaneNat :
      ((BitVec.setWidth width (BitVec.extractLsb' 0 8 byte)) <<< offset).toNat =
        (byte.toNat % 2 ^ 8) * 2 ^ offset := by
    simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    rw [hByteNat, Nat.mod_eq_of_lt hlane]
  have hOrLow :
      (byte.toNat % 2 ^ 8) * 2 ^ offset + value.toNat % 2 ^ offset =
        ((byte.toNat % 2 ^ 8) * 2 ^ offset) ||| (value.toNat % 2 ^ offset) := by
    calc
      _ = 2 ^ offset * (byte.toNat % 2 ^ 8) + value.toNat % 2 ^ offset := by
        rw [Nat.mul_comm]
      _ = (2 ^ offset * (byte.toNat % 2 ^ 8)) ||| (value.toNat % 2 ^ offset) :=
        Nat.two_pow_add_eq_or_of_lt hlow _
      _ = _ := by rw [Nat.mul_comm]
  have hOrAll :
      (value.toNat / 2 ^ (offset + 8)) * 2 ^ (offset + 8) +
        ((byte.toNat % 2 ^ 8) * 2 ^ offset + value.toNat % 2 ^ offset) =
      ((value.toNat / 2 ^ (offset + 8)) * 2 ^ (offset + 8)) |||
        (((byte.toNat % 2 ^ 8) * 2 ^ offset) ||| (value.toNat % 2 ^ offset)) := by
    calc
      _ = 2 ^ (offset + 8) * (value.toNat / 2 ^ (offset + 8)) +
          ((byte.toNat % 2 ^ 8) * 2 ^ offset + value.toNat % 2 ^ offset) := by
        rw [Nat.mul_comm]
      _ = (2 ^ (offset + 8) * (value.toNat / 2 ^ (offset + 8))) |||
          ((byte.toNat % 2 ^ 8) * 2 ^ offset + value.toNat % 2 ^ offset) :=
        Nat.two_pow_add_eq_or_of_lt hmid _
      _ = _ := by rw [Nat.mul_comm, hOrLow]
  unfold holFiniteWordSetByteBitVec
  rw [BitVec.toNat_or, BitVec.toNat_or, hHighNat, hLaneNat, hLowNat]
  calc
    _ = ((value.toNat / 2 ^ (offset + 8)) * 2 ^ (offset + 8)) |||
        (((byte.toNat % 2 ^ 8) * 2 ^ offset) ||| (value.toNat % 2 ^ offset)) := by
          rw [Nat.or_assoc]
    _ = (value.toNat / 2 ^ (offset + 8)) * 2 ^ (offset + 8) +
        ((byte.toNat % 2 ^ 8) * 2 ^ offset + value.toNat % 2 ^ offset) := hOrAll.symm
    _ = (value.toNat / 2 ^ (offset + 8)) * 2 ^ (offset + 8) +
        (byte.toNat % 2 ^ 8) * 2 ^ offset + value.toNat % 2 ^ offset := by omega
/-- A load model with HOL's dimension-derived byte alignment and the existing
    RISC-V byte extraction, alignment, and word-of-bytes operations. This is
    only the first operation-level bridge: the remaining imported word
    primitives still require a generic correspondence proof. -/
def holByteAlignedRiscVMemoryModel [NeZero width] (bigEndian : Bool) :
    PanMemoryModel (RiscV.Word width) :=
  let model := RiscV.panRiscVMemoryModelForEndian bigEndian
  { model with byteAlign := fun _ address => holByteAlignBitVec address }
/-! At the shipped RV64 configuration, the executed target byte-load helper
    also reduces to the same tagged HOL operation. This equation is stated on
    the explicit `CrepHolState` carrier and preserves both success and domain
    failure without assuming a successful target result. -/

theorem crepHolEvalMemLoadByte_riscv64_eq_panMemLoadByteHOL {σ : Type}
    (state : CrepHolState (BitVec 64) σ) (address : BitVec 64) :
    crepHolEvalMemLoadByte
        (RiscV.panRiscVMemoryModelForEndian state.bigEndian) (8 : BitVec 64)
        state address =
      (panMemLoadByteHOL
        (fun current => (state.memory current).toHolWordLab)
        (fun current => state.memaddrs current = true)
        state.bigEndian address).map (fun byte => BitVec.ofNat 64 byte.toNat) := by
  simp only [crepHolEvalMemLoadByte, panMemLoadByteHOL,
    RiscV.panRiscVMemoryModelForEndian]
  have haligned : RiscV.panRiscVByteAlign (8 : BitVec 64) address =
      panByteAlignHOL address := by
    have hprod := RiscV.panRiscVByteAlign_eight_eq_bitMask address
    have hhol : panByteAlignHOL address =
        BitVec.ofNat 64 ((address.toNat >>> 3) <<< 3) := by
      simp [panByteAlignHOL, show Nat.log2 (64 / 8) = 3 by decide,
        Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    exact hprod.trans hhol.symm
  simp only [haligned]
  cases hcell : state.memory (panByteAlignHOL address) with
  | word value =>
      by_cases hdomain : state.memaddrs (panByteAlignHOL address) = true
      · simp only [hcell, PanWordLab.toHolWordLab, hdomain,
          ↓reduceIte, Option.map_some]
        have hbyte := panGetByteHOL_eq_panRiscVGetByteEndian
          address value state.bigEndian
        have hlt := panRiscVGetByteEndian_toNat_lt_256
          address value state.bigEndian
        rw [hbyte]
        apply congrArg some
        let byte := RiscV.panRiscVGetByteEndian (8 : BitVec 64)
          address value state.bigEndian
        have hbyteVal : (UInt8.ofNat byte.toNat).toNat = byte.toNat :=
          UInt8.toNat_ofNat_of_lt hlt
        change byte = BitVec.ofNat 64 (UInt8.ofNat byte.toNat).toNat
        rw [hbyteVal]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_ofNat]
        exact (Nat.mod_eq_of_lt (by omega : byte.toNat < 2 ^ 64)).symm
      · simp [hdomain]

/-- All-width form of `crepHolEvalMemLoadByte_riscv64_eq_panMemLoadByteHOL`: at
    the canonical byte count `bytesInWord = width / 8`, the executed RISC-V
    byte-load helper equals the tagged Lean `panMemLoadByteHOL` widened to the
    word.  The alignment step is `panRiscVByteAlign_bytesInWord_eq_holByteAlignBitVec_lean`
    and the byte offset is `w2n a MOD d` (reversed when big endian).  Success
    and domain failure are both preserved.
    Width domain: this is an equality of Lean definitions at every positive width, but
    it is a HOL correspondence only for `width ≥ 8`.  Below width 8 the byte count `dimindex DIV 8` is 0. HOL's `byte_index` is still
    specified there (`w2n a MOD 0 = w2n a`, which Lean's `n % 0 = n` matches), but
    `byte_align` uses `LOG2 0`, which HOL leaves underspecified; the Lean alignment
    uses the chosen completion `Nat.log2 0 = 0`, with no HOL claim. So this does not
    establish an all-width HOL correspondence for the byte loads.
    Flapjack-only bridge (bead `flapjack-pxn.18.5.4.3.5`). -/
theorem crepHolEvalMemLoadByte_riscv_eq_panMemLoadByteHOL [NeZero width] {σ : Type}
    (state : CrepHolState (BitVec width) σ) (address : BitVec width) :
    crepHolEvalMemLoadByte
        (RiscV.panRiscVMemoryModelForEndian state.bigEndian) (BitVec.ofNat width (width / 8))
        state address =
      (panMemLoadByteHOL
        (fun current => (state.memory current).toHolWordLab)
        (fun current => state.memaddrs current = true)
        state.bigEndian address).map (fun byte => BitVec.ofNat width byte.toNat) := by
  simp only [crepHolEvalMemLoadByte, panMemLoadByteHOL,
    RiscV.panRiscVMemoryModelForEndian]
  have haligned : RiscV.panRiscVByteAlign (BitVec.ofNat width (width / 8)) address =
      panByteAlignHOL address :=
    panRiscVByteAlign_bytesInWord_eq_holByteAlignBitVec_lean address
  simp only [haligned]
  have hlt : width / 8 < 2 ^ width :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.lt_two_pow_self)
  have hbytes : (BitVec.ofNat width (width / 8)).toNat = width / 8 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  cases hcell : state.memory (panByteAlignHOL address) with
  | word value =>
      by_cases hdomain : state.memaddrs (panByteAlignHOL address) = true
      · simp only [hcell, PanWordLab.toHolWordLab, hdomain,
          ↓reduceIte, Option.map_some]
        apply congrArg some
        unfold panGetByteHOL RiscV.panRiscVGetByteEndian RiscV.panRiscVByteIndex
        rw [hbytes]
        dsimp only
        congr 1
        simp
      · simp [hdomain]

/-- All-width form of `crepRuntimeLoadByte_riscv64_eq_panMemLoadByteHOL`: the
    production `crepRuntimeLoadByte` at the canonical RISC-V runtime of a
    `CrepHolState` equals the tagged Lean `panMemLoadByteHOL`.
    Width domain: this is an equality of Lean definitions at every positive width, but
    it is a HOL correspondence only for `width ≥ 8`.  Below width 8 the byte count `dimindex DIV 8` is 0. HOL's `byte_index` is still
    specified there (`w2n a MOD 0 = w2n a`, which Lean's `n % 0 = n` matches), but
    `byte_align` uses `LOG2 0`, which HOL leaves underspecified; the Lean alignment
    uses the chosen completion `Nat.log2 0 = 0`, with no HOL claim. So this does not
    establish an all-width HOL correspondence for the byte loads. -/
theorem crepRuntimeLoadByte_riscv_eq_panMemLoadByteHOL [NeZero width] {σ : Type}
    (state : CrepHolState (BitVec width) σ) (address : BitVec width) :
    crepRuntimeLoadByte (riscvCrepWordTarget state.toRuntime) address =
      (panMemLoadByteHOL
        (fun current => (state.memory current).toHolWordLab)
        (fun current => state.memaddrs current = true)
        state.bigEndian address).map (fun byte => BitVec.ofNat width byte.toNat) := by
  calc
    crepRuntimeLoadByte (riscvCrepWordTarget state.toRuntime) address =
      panModelReadByte (RiscV.panRiscVMemoryModelForEndian state.bigEndian)
        state.memaddrs (crepRuntimeMemoryView state.memory)
        (BitVec.ofNat width (width / 8)) address state.bigEndian :=
          crepRuntimeLoadByte_wordTarget_eq_riscv state.toRuntime address
    _ = panModelReadByte (RiscV.panRiscVMemoryModelForEndian state.bigEndian)
        state.memaddrs
        (fun current => some (panTheWord (state.memory current)))
        (BitVec.ofNat width (width / 8)) address state.bigEndian := rfl
    _ = crepHolEvalMemLoadByte
        (RiscV.panRiscVMemoryModelForEndian state.bigEndian) (BitVec.ofNat width (width / 8))
        state address := by
          symm
          exact crepHolEvalMemLoadByte_eq_panModelReadByte _ _ _ _
    _ = _ := crepHolEvalMemLoadByte_riscv_eq_panMemLoadByteHOL state address

theorem crepRuntimeLoadByte_riscv64_eq_panMemLoadByteHOL {σ : Type}
    (state : CrepHolState (BitVec 64) σ) (address : BitVec 64) :
    crepRuntimeLoadByte (riscvCrepWordTarget state.toRuntime) address =
      (panMemLoadByteHOL
        (fun current => (state.memory current).toHolWordLab)
        (fun current => state.memaddrs current = true)
        state.bigEndian address).map (fun byte => BitVec.ofNat 64 byte.toNat) := by
  calc
    crepRuntimeLoadByte (riscvCrepWordTarget state.toRuntime) address =
      panModelReadByte (RiscV.panRiscVMemoryModelForEndian state.bigEndian)
        state.memaddrs (crepRuntimeMemoryView state.memory)
        (8 : BitVec 64) address state.bigEndian :=
          crepRuntimeLoadByte_wordTarget_eq_riscv state.toRuntime address
    _ = panModelReadByte (RiscV.panRiscVMemoryModelForEndian state.bigEndian)
        state.memaddrs
        (fun current => some (panTheWord (state.memory current)))
        (8 : BitVec 64) address state.bigEndian := rfl
    _ = crepHolEvalMemLoadByte
        (RiscV.panRiscVMemoryModelForEndian state.bigEndian) (8 : BitVec 64)
        state address := by
          symm
          exact crepHolEvalMemLoadByte_eq_panModelReadByte _ _ _ _
    _ = (panMemLoadByteHOL
        (fun current => (state.memory current).toHolWordLab)
        (fun current => state.memaddrs current = true)
        state.bigEndian address).map
          (fun byte => BitVec.ofNat 64 byte.toNat) :=
            crepHolEvalMemLoadByte_riscv64_eq_panMemLoadByteHOL state address

/-! RV64 Load32 uses the existing PanSem byte-assembly bridge after explicitly
    viewing a Crep word-lab memory as PanSem word cells. -/

theorem crepHolEvalMemLoad32_riscv64_eq_panMemLoad32HOL {σ : Type}
    (state : CrepHolState (BitVec 64) σ) (address : BitVec 64) :
    crepHolEvalMemLoad32
        (RiscV.panRiscVMemoryModelForEndian state.bigEndian) (8 : BitVec 64)
        state address =
      (panMemLoad32HOL
        (fun current => (state.memory current).toHolWordLab)
        (fun current => state.memaddrs current = true)
        state.bigEndian address).map (fun value => BitVec.ofNat 64 value.toNat) := by
  let source : PanSemState (BitVec 64) (FfiState σ) :=
    { locals := fun _ => none
      globals := fun _ => none
      structs := []
      code := []
      exceptionShapes := fun _ => none
      memory := fun current => some (.word (panTheWord (state.memory current)))
      memaddrs := state.memaddrs
      sharedMemaddrs := state.shMemaddrs
      clock := state.clock
      be := state.bigEndian
      ffi := state.ffi
      baseAddress := state.baseAddress
      topAddress := state.topAddress }
  have hget (byteAddress value : BitVec 64) :
      panSemBitVec64WordModel.getByte (8 : BitVec 64) byteAddress value
          state.bigEndian =
        (RiscV.panRiscVMemoryModelForEndian state.bigEndian).getByte
          (8 : BitVec 64) byteAddress value state.bigEndian := by
    rw [panSemBitVec64GetByte_eq_panRiscVGetByteEndian]
    simp [RiscV.panRiscVMemoryModelForEndian]
  have hmodel :
      panModelRead32
          (RiscV.panRiscVMemoryModelForEndian state.bigEndian)
          state.memaddrs
          (fun current => some (panTheWord (state.memory current)))
          (8 : BitVec 64) address state.bigEndian =
        (panSemBitVec64MemoryAccess source).read32
          (panSemBitVec64MemoryAccess source).domain source.memory
          panSemBitVec64BytesInWord address := by
    change panModelRead32
        (RiscV.panRiscVMemoryModelForEndian state.bigEndian)
        state.memaddrs
        (fun current => some (panTheWord (state.memory current)))
        (8 : BitVec 64) address state.bigEndian =
      panModelRead32 panSemBitVec64WordModel state.memaddrs
        (panValueWordMemory source.memory) (8 : BitVec 64) address state.bigEndian
    unfold panModelRead32
    have haligned :
        (RiscV.panRiscVMemoryModelForEndian state.bigEndian).aligned 4 address =
          panSemBitVec64WordModel.aligned 4 address := rfl
    have hbyteAlign :
        (RiscV.panRiscVMemoryModelForEndian state.bigEndian).byteAlign
            (8 : BitVec 64) address =
          panSemBitVec64WordModel.byteAlign (8 : BitVec 64) address := rfl
    rw [haligned, hbyteAlign]
    by_cases ha : panSemBitVec64WordModel.aligned 4 address = true
    · simp only [ite_eq_left ha]
      by_cases hd : state.memaddrs
          (panSemBitVec64WordModel.byteAlign (8 : BitVec 64) address) = true
      · simp only [hd, ↓reduceIte]
        change some ((RiscV.panRiscVMemoryModelForEndian state.bigEndian).wordOfBytes32
            state.bigEndian
            [(RiscV.panRiscVMemoryModelForEndian state.bigEndian).getByte
                (8 : BitVec 64) address
                (panTheWord (state.memory
                  (panSemBitVec64WordModel.byteAlign (8 : BitVec 64) address))) state.bigEndian,
             (RiscV.panRiscVMemoryModelForEndian state.bigEndian).getByte
                (8 : BitVec 64) (address + 1)
                (panTheWord (state.memory
                  (panSemBitVec64WordModel.byteAlign (8 : BitVec 64) address))) state.bigEndian,
             (RiscV.panRiscVMemoryModelForEndian state.bigEndian).getByte
                (8 : BitVec 64) (address + 2)
                (panTheWord (state.memory
                  (panSemBitVec64WordModel.byteAlign (8 : BitVec 64) address))) state.bigEndian,
             (RiscV.panRiscVMemoryModelForEndian state.bigEndian).getByte
                (8 : BitVec 64) (address + 3)
                (panTheWord (state.memory
                  (panSemBitVec64WordModel.byteAlign (8 : BitVec 64) address))) state.bigEndian]) =
          (some (panTheWord (state.memory
            (panSemBitVec64WordModel.byteAlign (8 : BitVec 64) address)))).bind
            (fun value => some (panSemBitVec64WordModel.wordOfBytes32 state.bigEndian
              [panSemBitVec64WordModel.getByte (8 : BitVec 64) address value state.bigEndian,
               panSemBitVec64WordModel.getByte (8 : BitVec 64) (address + 1) value state.bigEndian,
               panSemBitVec64WordModel.getByte (8 : BitVec 64) (address + 2) value state.bigEndian,
               panSemBitVec64WordModel.getByte (8 : BitVec 64) (address + 3) value state.bigEndian]))
        simp only [Option.bind_some]
        rw [← hget address
          (panTheWord (state.memory
            (panSemBitVec64WordModel.byteAlign (8 : BitVec 64) address)))]
        rw [← hget (address + 1)
          (panTheWord (state.memory
            (panSemBitVec64WordModel.byteAlign (8 : BitVec 64) address)))]
        rw [← hget (address + 2)
          (panTheWord (state.memory
            (panSemBitVec64WordModel.byteAlign (8 : BitVec 64) address)))]
        rw [← hget (address + 3)
          (panTheWord (state.memory
            (panSemBitVec64WordModel.byteAlign (8 : BitVec 64) address)))]
        rfl
      · cases hdom : state.memaddrs
            (panSemBitVec64WordModel.byteAlign (8 : BitVec 64) address) <;>
          simp_all
    · simp [ha]
  calc
    crepHolEvalMemLoad32
        (RiscV.panRiscVMemoryModelForEndian state.bigEndian) (8 : BitVec 64)
        state address =
      panModelRead32
        (RiscV.panRiscVMemoryModelForEndian state.bigEndian)
        state.memaddrs
        (fun current => some (panTheWord (state.memory current)))
        (8 : BitVec 64) address state.bigEndian :=
          crepHolEvalMemLoad32_eq_panModelRead32 _ _ _ _
    _ = (panSemBitVec64MemoryAccess source).read32
        (panSemBitVec64MemoryAccess source).domain source.memory
        panSemBitVec64BytesInWord address := hmodel
    _ = (panMemLoad32HOL
        (fun current => (state.memory current).toHolWordLab)
        (fun current => state.memaddrs current = true)
        state.bigEndian address).map
          (fun value => BitVec.ofNat 64 value.toNat) := by
            have hread := panSemBitVec64Read32_eq_panMemLoad32HOL
              source source.memory address
            have hmemory : panValueWordHOL source.memory =
                (fun current => (state.memory current).toHolWordLab) := by
              funext current
              cases hmem : state.memory current with
              | word value =>
                  simp [panValueWordHOL, source, hmem, panTheWord,
                    PanWordLab.toHolWordLab]
            have hdomain :
                (fun current =>
                  (source.memaddrs current &&
                    decide (panValueWordDefined source.memory current = true)) = true) =
                (fun current => state.memaddrs current = true) := by
              funext current
              cases hmem : state.memory current with
              | word value => cases hdomain : state.memaddrs current <;>
                  simp [source, panValueWordDefined, hdomain]
            simpa [hmemory, hdomain, source, panValueWordHOL, panValueWordDefined,
              panValueWordMemory, panSemBitVec64BytesInWord,
              panSemBitVec64MemoryAccess, panValueMemoryAccessOfModel,
              PanWordLab.toHolWordLab] using hread

/-- At the canonical byte count `bytesInWord = width / 8`, the RISC-V endian
    byte extractor equals the Lean `panGetByteHOL` (HOL `get_byte`) widened to
    the word.
    Width domain: this is an equality of Lean definitions at every positive width, but
    it is a HOL correspondence only for `width ≥ 8`.  Below width 8 the byte count `dimindex DIV 8` is 0. HOL's `byte_index` is still
    specified there (`w2n a MOD 0 = w2n a`, which Lean's `n % 0 = n` matches), but
    `byte_align` uses `LOG2 0`, which HOL leaves underspecified; the Lean alignment
    uses the chosen completion `Nat.log2 0 = 0`, with no HOL claim. So this does not
    establish an all-width HOL correspondence for the byte loads. -/
theorem panRiscVGetByteEndian_bytesInWord_eq_panGetByteHOL [NeZero width]
    (address value : BitVec width) (bigEndian : Bool) :
    RiscV.panRiscVGetByteEndian (BitVec.ofNat width (width / 8)) address value bigEndian =
      BitVec.ofNat width (panGetByteHOL address value bigEndian).toNat := by
  have hlt : width / 8 < 2 ^ width :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.lt_two_pow_self)
  have hbytes : (BitVec.ofNat width (width / 8)).toNat = width / 8 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  unfold panGetByteHOL RiscV.panRiscVGetByteEndian RiscV.panRiscVByteIndex
  rw [hbytes]
  dsimp only
  congr 1
  simp

/-- HOL `mem_load_32` assembles its four bytes at `word32` and `eval` widens the
    result with `w2w`; the RISC-V model assembles directly at the word width.
    Because every byte is `< 256`, the four-byte sum is `< 2^32`, so the two
    assemblies agree for any word width (a pure arithmetic fact about the two
    Lean definitions). -/
theorem panRiscVWordOfBytes_eq_widen32 [NeZero width] (bigEndian : Bool)
    (b0 b1 b2 b3 : BitVec width) (h0 : b0.toNat < 256) (h1 : b1.toNat < 256)
    (h2 : b2.toNat < 256) (h3 : b3.toNat < 256) :
    RiscV.panRiscVWordOfBytes (width := width) bigEndian [b0, b1, b2, b3] =
      BitVec.ofNat width
        (RiscV.panRiscVWordOfBytes (width := 32) bigEndian
          ([b0, b1, b2, b3].map (fun byte => BitVec.ofNat 32 byte.toNat))).toNat := by
  have e0 : (BitVec.ofNat 32 b0.toNat).toNat = b0.toNat := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have e1 : (BitVec.ofNat 32 b1.toNat).toNat = b1.toNat := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have e2 : (BitVec.ofNat 32 b2.toNat).toNat = b2.toNat := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have e3 : (BitVec.ofNat 32 b3.toNat).toNat = b3.toNat := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold RiscV.panRiscVWordOfBytes
  simp only [List.map_cons, List.map_nil, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, e0, e1, e2, e3, show (256 : Nat) ^ 2 = 65536 from rfl,
    show (256 : Nat) ^ 3 = 16777216 from rfl]
  cases bigEndian
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · simp only [↓reduceIte]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- All-width form of `crepHolEvalMemLoad32_riscv64_eq_panMemLoad32HOL`: at the
    canonical byte count `bytesInWord = width / 8`, the executed RISC-V 32-bit
    load helper equals the tagged Lean `panMemLoad32HOL` widened to the word.
    Alignment, domain failure and success are all preserved.
    Width domain: this is an equality of Lean definitions at every positive width, but
    it is a HOL correspondence only for `width ≥ 8`.  Below width 8 the byte count `dimindex DIV 8` is 0. HOL's `byte_index` is still
    specified there (`w2n a MOD 0 = w2n a`, which Lean's `n % 0 = n` matches), but
    `byte_align` uses `LOG2 0`, which HOL leaves underspecified; the Lean alignment
    uses the chosen completion `Nat.log2 0 = 0`, with no HOL claim. So this does not
    establish an all-width HOL correspondence for the byte loads.
    Flapjack-only bridge (bead `flapjack-pxn.18.5.4.3.6`). -/
theorem crepHolEvalMemLoad32_riscv_eq_panMemLoad32HOL [NeZero width] {σ : Type}
    (state : CrepHolState (BitVec width) σ) (address : BitVec width) :
    crepHolEvalMemLoad32
        (RiscV.panRiscVMemoryModelForEndian state.bigEndian) (BitVec.ofNat width (width / 8))
        state address =
      (panMemLoad32HOL
        (fun current => (state.memory current).toHolWordLab)
        (fun current => state.memaddrs current = true)
        state.bigEndian address).map (fun value => BitVec.ofNat width value.toNat) := by
  have haligned : RiscV.panRiscVByteAlign (BitVec.ofNat width (width / 8)) address =
      panByteAlignHOL address :=
    panRiscVByteAlign_bytesInWord_eq_holByteAlignBitVec_lean address
  have hbyte : ∀ a : BitVec width,
      (BitVec.ofNat width (panGetByteHOL a (panTheWord (state.memory (panByteAlignHOL address)))
        state.bigEndian).toNat).toNat < 256 := by
    intro a
    rw [BitVec.toNat_ofNat]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (UInt8.toNat_lt _)
  unfold crepHolEvalMemLoad32 panMemLoad32HOL
  simp only [RiscV.panRiscVMemoryModelForEndian, RiscV.aligned, haligned,
    panRiscVGetByteEndian_bytesInWord_eq_panGetByteHOL]
  by_cases h4 : address.toNat % 4 = 0
  · simp only [h4, decide_true, Bool.and_true, ↓reduceIte]
    cases hcell : state.memory (panByteAlignHOL address) with
    | word value =>
        have hv : panTheWord (state.memory (panByteAlignHOL address)) = value := by
          rw [hcell]; rfl
        by_cases hdomain : state.memaddrs (panByteAlignHOL address) = true
        · simp only [PanWordLab.toHolWordLab, hdomain, ↓reduceIte, Option.map_some]
          apply congrArg some
          rw [← hv]
          exact panRiscVWordOfBytes_eq_widen32 _ _ _ _ _
            (hbyte _) (hbyte _) (hbyte _) (hbyte _)
        · simp [hdomain]
  · simp [h4]

/-- All-width form of `crepRuntimeLoad32_riscv64_eq_panMemLoad32HOL`.
    Width domain: this is an equality of Lean definitions at every positive width, but
    it is a HOL correspondence only for `width ≥ 8`.  Below width 8 the byte count `dimindex DIV 8` is 0. HOL's `byte_index` is still
    specified there (`w2n a MOD 0 = w2n a`, which Lean's `n % 0 = n` matches), but
    `byte_align` uses `LOG2 0`, which HOL leaves underspecified; the Lean alignment
    uses the chosen completion `Nat.log2 0 = 0`, with no HOL claim. So this does not
    establish an all-width HOL correspondence for the byte loads. -/
theorem crepRuntimeLoad32_riscv_eq_panMemLoad32HOL [NeZero width] {σ : Type}
    (state : CrepHolState (BitVec width) σ) (address : BitVec width) :
    crepRuntimeLoad32 (riscvCrepWordTarget state.toRuntime) address =
      (panMemLoad32HOL
        (fun current => (state.memory current).toHolWordLab)
        (fun current => state.memaddrs current = true)
        state.bigEndian address).map (fun value => BitVec.ofNat width value.toNat) := by
  calc
    crepRuntimeLoad32 (riscvCrepWordTarget state.toRuntime) address =
      panModelRead32 (RiscV.panRiscVMemoryModelForEndian state.bigEndian)
        state.memaddrs (crepRuntimeMemoryView state.memory)
        (BitVec.ofNat width (width / 8)) address state.bigEndian :=
          crepRuntimeLoad32_wordTarget_eq_riscv state.toRuntime address
    _ = panModelRead32 (RiscV.panRiscVMemoryModelForEndian state.bigEndian)
        state.memaddrs (fun current => some (panTheWord (state.memory current)))
        (BitVec.ofNat width (width / 8)) address state.bigEndian := rfl
    _ = crepHolEvalMemLoad32
        (RiscV.panRiscVMemoryModelForEndian state.bigEndian) (BitVec.ofNat width (width / 8))
        state address := by
          symm
          exact crepHolEvalMemLoad32_eq_panModelRead32 _ _ _ _
    _ = _ := crepHolEvalMemLoad32_riscv_eq_panMemLoad32HOL state address

theorem crepRuntimeLoad32_riscv64_eq_panMemLoad32HOL {σ : Type}
    (state : CrepHolState (BitVec 64) σ) (address : BitVec 64) :
    crepRuntimeLoad32 (riscvCrepWordTarget state.toRuntime) address =
      (panMemLoad32HOL
        (fun current => (state.memory current).toHolWordLab)
        (fun current => state.memaddrs current = true)
        state.bigEndian address).map (fun value => BitVec.ofNat 64 value.toNat) := by
  calc
    crepRuntimeLoad32 (riscvCrepWordTarget state.toRuntime) address =
      panModelRead32 (RiscV.panRiscVMemoryModelForEndian state.bigEndian)
        state.memaddrs (crepRuntimeMemoryView state.memory)
        (8 : BitVec 64) address state.bigEndian :=
          crepRuntimeLoad32_wordTarget_eq_riscv state.toRuntime address
    _ = panModelRead32 (RiscV.panRiscVMemoryModelForEndian state.bigEndian)
        state.memaddrs (fun current => some (panTheWord (state.memory current)))
        (8 : BitVec 64) address state.bigEndian := rfl
    _ = crepHolEvalMemLoad32
        (RiscV.panRiscVMemoryModelForEndian state.bigEndian) (8 : BitVec 64)
        state address := by
          symm
          exact crepHolEvalMemLoad32_eq_panModelRead32 _ _ _ _
    _ = (panMemLoad32HOL
        (fun current => (state.memory current).toHolWordLab)
        (fun current => state.memaddrs current = true)
        state.bigEndian address).map
          (fun value => BitVec.ofNat 64 value.toNat) :=
            crepHolEvalMemLoad32_riscv64_eq_panMemLoad32HOL state address
/-- Source-shaped Lean translation of HOL `crepSem$eval_def` for every
    positive BitVec word width. It is untagged because the arbitrary HOL word
    carrier remains unrepresented; `evalCrepRuntimeExp_toRuntime_eq` proves
    this translation agrees constructor by constructor with production.

    Source-reviewed disposition for HOL
    `eval_nested_decs_seq_res_var_eq`
    (`pan_to_crepProofScript.sml:596-620`): HOL implicitly universally
    quantifies `es`, `ns`, `t`, `ev`, and `p`. The four premises are successful
    evaluation of every expression in `es`, equal lengths of `ns` and `es`,
    `distinct_lists ns (FLAT (MAP var_cexp es))`, and distinct `ns`. The
    conclusion is the exact equation for evaluating `nested_decs ns es p`:
    evaluate `p` after installing `ZIP (ns, ev)`, then restore each original
    local with `FOLDL res_var` over `ZIP (ns, MAP (FLOOKUP t.locals) ns)`.
    `nestedDecsHOL` ports only the syntax. This expression evaluator is over
    production `CrepExp` and `CrepHolState`, while the theorem quantifies over
    the full Crep program and finite-map state; `evalCrepClockProg` likewise
    covers only restricted production `CrepClockProg`/`CrepHolState`. There is
    no full evaluator over `CrepProgHOL`/`CrepExpHOL` and
    `CrepSemHOLState`, so the equation cannot be stated with these evaluators
    and no tag is claimed. The faithful replacement is
    `flapjack-4ac.5.19.1`, dependent on `flapjack-4ac.5.82` and exact Crep
    carriers `flapjack-pxn.18.3.5.8.8`. -/
def evalCrepHolExp [NeZero width]
    (state : CrepHolState (RiscV.Word width) σ) :
    CrepExp (RiscV.Word width) → Option (RiscV.Word width)
  | .const value => some value
  | .var name => (state.locals name).map panTheWord
  | .load address => do
      let address ← evalCrepHolExp state address
      if state.memaddrs address then some (panTheWord (state.memory address)) else none
  | .load32 address => do
      let address ← evalCrepHolExp state address
      crepHolEvalMemLoad32
        (RiscV.panRiscVMemoryModelForEndian state.bigEndian)
        (BitVec.ofNat width (width / 8)) state address
  | .loadByte address => do
      let address ← evalCrepHolExp state address
      crepHolEvalMemLoadByte
        (RiscV.panRiscVMemoryModelForEndian state.bigEndian)
        (BitVec.ofNat width (width / 8)) state address
  | .loadGlob address => (state.globals address).map panTheWord
  | .op operator expressions => do
      let values ← expressions.mapM (evalCrepHolExp state)
      wordOpHOL operator values
  | .crepOp .mul [left, right] => do
      let left ← evalCrepHolExp state left
      let right ← evalCrepHolExp state right
      pure (left * right)
  | .crepOp _ _ => none
  | .cmp operator left right => do
      let left ← evalCrepHolExp state left
      let right ← evalCrepHolExp state right
      pure (evalPanCmp operator left right)
  | .shift operator left right => do
      let left ← evalCrepHolExp state left
      let right ← evalCrepHolExp state right
      evalPanShiftFull operator left right
  | .baseAddr => some state.baseAddress
  | .topAddr => some state.topAddress
termination_by expression => sizeOf expression

/-- HOL-shaped complete result wrapper for the raw word evaluator above. -/
def evalCrepHolExpWordLab [NeZero width]
    (state : CrepHolState (RiscV.Word width) σ) :
    CrepExp (RiscV.Word width) → Option (PanWordLab (RiscV.Word width)) :=
  fun expression => (evalCrepHolExp state expression).map PanWordLab.word

/-! HOL evaluator source shape for the Fin-index word representation is
    obtained by transporting the existing source-shaped evaluator through the
    carrier equivalence. Its production relation is proved below for every
    constructor, but the concrete `Fin width` index still does not represent
    every HOL finite dimension type. -/
/-! Target helpers for the production evaluator relation, retaining the
    source state memory/domain fields. -/

private theorem crepHolState_load32 [NeZero width]
    (state : CrepHolState (RiscV.Word width) σ) (address : RiscV.Word width) :
    crepRuntimeLoad32 (riscvCrepWordTarget state.toRuntime) address =
      panModelRead32 (RiscV.panRiscVMemoryModelForEndian state.bigEndian)
        state.memaddrs (fun current => some (panTheWord (state.memory current)))
        (BitVec.ofNat width (width / 8)) address state.bigEndian := by
  have hmem : crepRuntimeMemoryView state.memory =
      (fun current => some (panTheWord (state.memory current))) := rfl
  rw [← hmem]
  exact crepRuntimeLoad32_wordTarget_eq_riscv (state.toRuntime) address

private theorem crepHolState_loadByte [NeZero width]
    (state : CrepHolState (RiscV.Word width) σ) (address : RiscV.Word width) :
    crepRuntimeLoadByte (riscvCrepWordTarget state.toRuntime) address =
      panModelReadByte (RiscV.panRiscVMemoryModelForEndian state.bigEndian)
        state.memaddrs (fun current => some (panTheWord (state.memory current)))
        (BitVec.ofNat width (width / 8)) address state.bigEndian := by
  have hmem : crepRuntimeMemoryView state.memory =
      (fun current => some (panTheWord (state.memory current))) := rfl
  rw [← hmem]
  exact crepRuntimeLoadByte_wordTarget_eq_riscv (state.toRuntime) address

/-! Flapjack-only all-constructor correspondence for the positive-width
BitVec adapter. -/
theorem evalCrepRuntimeExp_toRuntime_eq [NeZero width]
    (state : CrepHolState (RiscV.Word width) σ)
    (expression : CrepExp (RiscV.Word width)) :
    evalCrepRuntimeExp (riscvCrepWordTarget state.toRuntime) expression =
      evalCrepHolExp state expression := by
  have evalExpsMapM (targetState : CrepRuntimeState (RiscV.Word width) σ) :
      ∀ expressions,
        evalCrepRuntimeExps targetState expressions =
          expressions.mapM (evalCrepRuntimeExp targetState) := by
    intro xs
    induction xs with
    | nil => simp [evalCrepRuntimeExps]
    | cons head tail ih => simp [evalCrepRuntimeExps, ih]
  induction expression using
      (CrepExp.rec (motive_2 := fun expressions =>
        (∀ e, e ∈ expressions → ∀ (state : CrepHolState (RiscV.Word width) σ),
          evalCrepRuntimeExp (riscvCrepWordTarget state.toRuntime) e =
            evalCrepHolExp state e) ∧
        (∀ (state : CrepHolState (RiscV.Word width) σ),
          evalCrepRuntimeExps (riscvCrepWordTarget state.toRuntime) expressions =
            expressions.mapM (evalCrepHolExp state))))
      generalizing state
  case const value => simp [evalCrepRuntimeExp, evalCrepHolExp,
    riscvCrepWordTarget, CrepHolState.toRuntime]
  case var name => simp [evalCrepRuntimeExp, evalCrepHolExp,
    riscvCrepWordTarget, CrepHolState.toRuntime]
  case load address ih =>
    simp only [evalCrepRuntimeExp, evalCrepHolExp]
    rw [ih state]
    simp [riscvCrepWordTarget, CrepHolState.toRuntime, crepRuntimeLoad,
      panTheWord]
    rfl
  case load32 address ih =>
    simp only [evalCrepRuntimeExp, evalCrepHolExp]
    rw [ih state]
    simp [crepHolState_load32, crepHolEvalMemLoad32_eq_panModelRead32]
  case loadByte address ih =>
    simp only [evalCrepRuntimeExp, evalCrepHolExp]
    rw [ih state]
    simp [crepHolState_loadByte, crepHolEvalMemLoadByte_eq_panModelReadByte]
  case loadGlob address => simp [evalCrepRuntimeExp, evalCrepHolExp,
    riscvCrepWordTarget, CrepHolState.toRuntime]
  case op operator expressions ih =>
    simp only [evalCrepRuntimeExp, evalCrepHolExp]
    rw [← evalExpsMapM (riscvCrepWordTarget state.toRuntime) expressions]
    rw [ih.2 state]
    simp [RiscV.panRiscVWordOp,
      wordOpHOL, wordOp,
      CrepHolState.toRuntime, riscvCrepWordTarget,
      RiscV.panRiscVMemoryModelForEndian]
  case crepOp operator expressions ih =>
    cases operator <;> cases expressions with
    | nil => simp [evalCrepRuntimeExp, evalCrepHolExp]
    | cons head tail => cases tail with
      | nil => simp [evalCrepRuntimeExp, evalCrepHolExp]
      | cons second tail => cases tail with
        | nil =>
          simp only [evalCrepRuntimeExp, evalCrepHolExp]
          rw [ih.1 head (by simp) state, ih.1 second (by simp) state]
          simp [crepOpCrep]
        | cons extra rest => simp [evalCrepRuntimeExp, evalCrepHolExp]
  case cmp operator left right ihl ihr =>
    simp only [evalCrepRuntimeExp, evalCrepHolExp]
    rw [ihl, ihr]
    simp [CrepHolState.toRuntime, riscvCrepWordTarget,
      RiscV.panRiscVMemoryModelForEndian, panRiscVCmp_eq_evalPanCmp]
  case shift operator left right ihl ihr =>
    simp only [evalCrepRuntimeExp, evalCrepHolExp]
    rw [ihl, ihr]
    simp [CrepHolState.toRuntime, riscvCrepWordTarget,
      RiscV.panRiscVMemoryModelForEndian, panRiscVShift_eq_evalPanShiftFull]
  case baseAddr => simp [evalCrepRuntimeExp, evalCrepHolExp,
    riscvCrepWordTarget, CrepHolState.toRuntime]
  case topAddr => simp [evalCrepRuntimeExp, evalCrepHolExp,
    riscvCrepWordTarget, CrepHolState.toRuntime]
  case nil => simp [evalCrepRuntimeExps]
  case cons head tail ihHead ihTail =>
    constructor
    · intro e he state
      simp only [List.mem_cons] at he
      rcases he with he | he
      · subst e
        exact ihHead state
      · exact ihTail.1 e he state
    · intro state
      simp [evalCrepRuntimeExps, ihHead state, ihTail.2 state]
end Flapjack
