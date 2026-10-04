import Flapjack.RiscV.L3.Defs.IntegerStore
import Flapjack.Misc.Alignment

/-! Flapjack-specific byte consequences of the actual native memory definitions.
No independently named HOL theorem is claimed. These lemmas retain modular
addresses and arbitrary native states; full encoder source obligations remain
in the original Mem constructor, rather than being premises on its conclusion.
-/
set_option autoImplicit false
namespace Flapjack.RiscV.L3.Step.ByteMemory
open Flapjack RiscV.L3

/-- The lowest byte of the literal native word write, for every word index. -/
theorem memory_write_word_low_byte (a : BitVec 61) (v : BitVec 64)
    (s : riscv_state) :
    («write'MEM» (v,a) s).MEM8 (a.setWidth 64 <<< 3) =
      RiscV.L3.holWordExtract 8 7 0 v := by
  simp [«write'MEM», holUpdate]

/-- Every byte of the literal native word write, including modular address wrap. -/
theorem memory_write_word_byte (a : BitVec 61) (v : BitVec 64)
    (s : riscv_state) (i : Fin 8) :
    («write'MEM» (v,a) s).MEM8
      ((a.setWidth 64 <<< 3) + BitVec.ofNat 64 i.val) =
      RiscV.L3.holWordExtract 8 (i.val * 8 + 7) (i.val * 8) v := by
  have cases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨
      i.val = 4 ∨ i.val = 5 ∨ i.val = 6 ∨ i.val = 7 := by omega
  rcases cases with h | h | h | h | h | h | h | h <;>
    simp [«write'MEM», holUpdate, h]

/-- Every byte of the literal little-endian word read. -/
theorem memory_read_word_byte (a : BitVec 61) (s : riscv_state) (i : Fin 8) :
    RiscV.L3.holWordExtract 8 (i.val * 8 + 7) (i.val * 8) (MEM a s) =
      s.MEM8 ((a.setWidth 64 <<< 3) + BitVec.ofNat 64 i.val) := by
  have cases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨
      i.val = 4 ∨ i.val = 5 ∨ i.val = 6 ∨ i.val = 7 := by omega
  have extract (w : BitVec 64) :
      RiscV.L3.holWordExtract 8 (i.val * 8 + 7) (i.val * 8) w =
        w.extractLsb' (i.val * 8) 8 := by
    apply BitVec.eq_of_toNat_eq
    have bound : i.val * 8 + 7 < 64 := by omega
    have size : i.val * 8 + 7 + 1 - i.val * 8 = 8 := by omega
    simp [size, RiscV.L3.holWordExtract, BitVec.extractLsb'_toNat, Nat.min_eq_left (by omega : i.val * 8 + 7 ≤ 63)]
  rw [extract]
  rcases cases with h | h | h | h | h | h | h | h <;>
    (apply BitVec.eq_of_getLsbD_eq; intro j hj;
     simp only [MEM, h, BitVec.setWidth_eq, BitVec.getLsbD_extractLsb'];
     simp only [BitVec.getLsbD_append];
     have j15 : j ≤ 15 := by omega;
     have j23 : j ≤ 23 := by omega;
     have j31 : j ≤ 31 := by omega;
     have j39 : j ≤ 39 := by omega;
     have j47 : j ≤ 47 := by omega;
     have j55 : j ≤ 55 := by omega;
     simp_all +arith)

/-- Literal raw read at a word-aligned address; no state restriction. -/
theorem memory_raw_read_word (a : BitVec 61) (s : riscv_state) :
    rawReadData (a.setWidth 64 <<< 3) s = MEM a s := by
  have lo : RiscV.L3.holWordExtract 3 2 0 (a.setWidth 64 <<< 3) = 0 := by
    apply BitVec.eq_of_toNat_eq
    simp [RiscV.L3.holWordExtract, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have hi : RiscV.L3.holWordExtract 61 63 3 (a.setWidth 64 <<< 3) = a := by
    apply BitVec.eq_of_toNat_eq
    have bound := a.isLt
    have product : a.toNat * 8 < 18446744073709551616 := by omega
    simp [RiscV.L3.holWordExtract, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt product, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt bound]
  dsimp only [rawReadData]
  rw [lo, hi]
  simp

/-- Literal eight-byte raw write at every word-aligned address. -/
theorem memory_raw_write_word (a : BitVec 61) (v : BitVec 64)
    (s : riscv_state) :
    rawWriteData (a.setWidth 64 <<< 3, v, 8) s = «write'MEM» (v,a) s := by
  have lo : RiscV.L3.holWordExtract 3 2 0 (a.setWidth 64 <<< 3) = 0 := by
    apply BitVec.eq_of_toNat_eq
    simp [RiscV.L3.holWordExtract, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have hi : RiscV.L3.holWordExtract 61 63 3 (a.setWidth 64 <<< 3) = a := by
    apply BitVec.eq_of_toNat_eq
    have bound := a.isLt
    have product : a.toNat * 8 < 18446744073709551616 := by omega
    simp [RiscV.L3.holWordExtract, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt product, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt bound]
  dsimp only [rawWriteData]
  rw [lo, hi]
  simp
  change «write'MEM» (v &&& BitVec.allOnes 64,a) s = _
  rw [BitVec.and_allOnes]

/-- Complete pointwise frame outside the eight literal word-write addresses.
The address conditions describe this helper's written region; they are not
extra assumptions on the original encoder theorem. -/
theorem memory_write_word_frame (a : BitVec 61) (v : BitVec 64)
    (s : riscv_state) (x : BitVec 64)
    (outside : ∀ i : Nat, i < 8 → x ≠ (a.setWidth 64 <<< 3) + BitVec.ofNat 64 i) :
    («write'MEM» (v,a) s).MEM8 x = s.MEM8 x := by
  have h0 := outside 0 (by decide)
  have h1 := outside 1 (by decide)
  have h2 := outside 2 (by decide)
  have h3 := outside 3 (by decide)
  have h4 := outside 4 (by decide)
  have h5 := outside 5 (by decide)
  have h6 := outside 6 (by decide)
  have h7 := outside 7 (by decide)
  simp only [BitVec.add_zero] at h0
  simp_all [«write'MEM», holUpdate, eq_comm]

/-- Full-word raw load bytes, derived from the actual native read. -/
theorem memory_raw_read_word_byte (a : BitVec 61) (s : riscv_state) (i : Fin 8) :
    RiscV.L3.holWordExtract 8 (i.val * 8 + 7) (i.val * 8)
      (rawReadData (a.setWidth 64 <<< 3) s) =
      s.MEM8 ((a.setWidth 64 <<< 3) + BitVec.ofNat 64 i.val) := by
  rw [memory_raw_read_word]
  exact memory_read_word_byte a s i

/-- Full-word raw store bytes, with arbitrary values and modular addresses. -/
theorem memory_raw_write_word_byte (a : BitVec 61) (v : BitVec 64)
    (s : riscv_state) (i : Fin 8) :
    (rawWriteData (a.setWidth 64 <<< 3,v,8) s).MEM8
      ((a.setWidth 64 <<< 3) + BitVec.ofNat 64 i.val) =
      RiscV.L3.holWordExtract 8 (i.val * 8 + 7) (i.val * 8) v := by
  rw [memory_raw_write_word]
  exact memory_write_word_byte a v s i

/-- Full-word raw store preserves every address outside its eight bytes. -/
theorem memory_raw_write_word_frame (a : BitVec 61) (v : BitVec 64)
    (s : riscv_state) (x : BitVec 64)
    (outside : ∀ i : Nat, i < 8 → x ≠ (a.setWidth 64 <<< 3) + BitVec.ofNat 64 i) :
    (rawWriteData (a.setWidth 64 <<< 3,v,8) s).MEM8 x = s.MEM8 x := by
  rw [memory_raw_write_word]
  exact memory_write_word_frame a v s x outside

/-- Word-aligned addresses reconstruct from their literal native word index.
This is an address arithmetic helper; the original LD/SD source guards supply
alignment in the full constructor proof. -/
theorem memory_aligned_address (p : BitVec 64) (aligned : holAligned 3 p = true) :
    (RiscV.L3.holWordExtract 61 63 3 p).setWidth 64 <<< 3 = p := by
  have low := (holAligned_iff 3 p).mp aligned
  apply BitVec.eq_of_toNat_eq
  have bound := p.isLt
  simp [RiscV.L3.holWordExtract, BitVec.toNat_shiftLeft,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  simp at low bound
  omega

/-- Aligned arbitrary-address raw word load, without restricting native state. -/
theorem memory_raw_read_aligned (p : BitVec 64) (s : riscv_state)
    (aligned : holAligned 3 p = true) :
    rawReadData p s = MEM (RiscV.L3.holWordExtract 61 63 3 p) s := by
  have result := memory_raw_read_word (RiscV.L3.holWordExtract 61 63 3 p) s
  rw [memory_aligned_address p aligned] at result
  exact result

/-- Aligned arbitrary-address raw full-word store, preserving the actual model. -/
theorem memory_raw_write_aligned (p v : BitVec 64) (s : riscv_state)
    (aligned : holAligned 3 p = true) :
    rawWriteData (p,v,8) s = «write'MEM» (v,RiscV.L3.holWordExtract 61 63 3 p) s := by
  have result := memory_raw_write_word (RiscV.L3.holWordExtract 61 63 3 p) v s
  rw [memory_aligned_address p aligned] at result
  exact result

/-- Every byte address decomposes into its native word index and low offset,
including the final word of the modular address space. -/
theorem memory_address_decomposition (p : BitVec 64) :
    ((RiscV.L3.holWordExtract 61 63 3 p).setWidth 64 <<< 3) +
      (RiscV.L3.holWordExtract 3 2 0 p).setWidth 64 = p := by
  apply BitVec.eq_of_toNat_eq
  have bound := p.isLt
  simp [RiscV.L3.holWordExtract, BitVec.toNat_shiftLeft,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, BitVec.toNat_add]
  simp at bound
  omega

/-- The native low address offset is always one of the eight word bytes. -/
theorem memory_address_offset_bound (p : BitVec 64) :
    (RiscV.L3.holWordExtract 3 2 0 p).toNat < 8 := by
  exact (RiscV.L3.holWordExtract 3 2 0 p).isLt

private theorem memory_extract_low8 (w : BitVec 64) :
    RiscV.L3.holWordExtract 8 7 0 w = w.extractLsb' 0 8 := by
  apply BitVec.eq_of_toNat_eq
  simp [RiscV.L3.holWordExtract, BitVec.extractLsb'_toNat]

private theorem memory_extract_low64 (w : BitVec 128) :
    RiscV.L3.holWordExtract 64 63 0 w = w.extractLsb' 0 64 := by
  apply BitVec.eq_of_toNat_eq
  simp [RiscV.L3.holWordExtract, BitVec.extractLsb'_toNat]

private theorem memory_extract_offset8 (w : BitVec 64) (i : Fin 8) :
    RiscV.L3.holWordExtract 8 (i.val * 8 + 7) (i.val * 8) w =
      w.extractLsb' (i.val * 8) 8 := by
  apply BitVec.eq_of_toNat_eq
  have bound : i.val * 8 + 7 ≤ 63 := by omega
  have size : i.val * 8 + 7 + 1 - i.val * 8 = 8 := by omega
  simp [RiscV.L3.holWordExtract, BitVec.extractLsb'_toNat,
    Nat.min_eq_left bound, size]

/-- The low byte of an arbitrary-address raw native read is exactly MEM8.
No alignment or state-validity assumption is needed for this literal operation. -/
theorem memory_raw_read_low_byte (p : BitVec 64) (s : riscv_state) :
    RiscV.L3.holWordExtract 8 7 0 (rawReadData p s) = s.MEM8 p := by
  let i : Fin 8 := ⟨(RiscV.L3.holWordExtract 3 2 0 p).toNat,
    memory_address_offset_bound p⟩
  have bytes := memory_read_word_byte (RiscV.L3.holWordExtract 61 63 3 p) s i
  have address : (RiscV.L3.holWordExtract 3 2 0 p).setWidth 64 =
      BitVec.ofNat 64 i.val := by
    apply BitVec.eq_of_toNat_eq
    simp [i]
  rw [← address, memory_address_decomposition] at bytes
  rw [← bytes, memory_extract_offset8, memory_extract_low8]
  dsimp only [rawReadData]
  by_cases zero : (RiscV.L3.holWordExtract 3 2 0 p).toNat = 0
  · simp [zero, i]
  · simp only [beq_iff_eq, zero, ↓reduceIte, memory_extract_low64]
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have offset := memory_address_offset_bound p
    have sumBound : (RiscV.L3.holWordExtract 3 2 0 p).toNat * 8 + j < 64 := by omega
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_sshiftRight]
    simp only [i] at *
    simp [hj, sumBound, show ¬128 ≤ j by omega,
      show (RiscV.L3.holWordExtract 3 2 0 p).toNat * 8 + j < 128 by omega]
    simp only [show j < 64 by omega, decide_true, Bool.true_and]
    change (MEM (RiscV.L3.holWordExtract 61 63 3 p + 1) s ++
      MEM (RiscV.L3.holWordExtract 61 63 3 p) s).getLsbD
        ((RiscV.L3.holWordExtract 3 2 0 p).toNat * 8 + j) =
      (MEM (RiscV.L3.holWordExtract 61 63 3 p) s).getLsbD
        ((RiscV.L3.holWordExtract 3 2 0 p).toNat * 8 + j)
    rw [BitVec.getLsbD_append, if_pos sumBound]


/-- Partial raw read within one native word. The arithmetic region condition
is discharged from the original source alignment in full encoder cases. -/
theorem memory_raw_read_within_word (p : BitVec 64) (s : riscv_state)
    (n : Nat) (within : (RiscV.L3.holWordExtract 3 2 0 p).toNat + n ≤ 8) :
    (rawReadData p s).extractLsb' 0 (n * 8) =
      (MEM (RiscV.L3.holWordExtract 61 63 3 p) s).extractLsb'
        ((RiscV.L3.holWordExtract 3 2 0 p).toNat * 8) (n * 8) := by
  dsimp only [rawReadData]
  by_cases zero : (RiscV.L3.holWordExtract 3 2 0 p).toNat = 0
  · simp [zero]
  · simp only [beq_iff_eq, zero, ↓reduceIte, memory_extract_low64]
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have sumBound : (RiscV.L3.holWordExtract 3 2 0 p).toNat * 8 + j < 64 := by omega
    have j64 : j < 64 := by omega
    have j128 : ¬128 ≤ j := by omega
    have sum128 : (RiscV.L3.holWordExtract 3 2 0 p).toNat * 8 + j < 128 := by omega
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_sshiftRight]
    simp [hj, j64, j128, sum128]
    change (MEM (RiscV.L3.holWordExtract 61 63 3 p + 1) s ++
      MEM (RiscV.L3.holWordExtract 61 63 3 p) s).getLsbD
        ((RiscV.L3.holWordExtract 3 2 0 p).toNat * 8 + j) =
      (MEM (RiscV.L3.holWordExtract 61 63 3 p) s).getLsbD
        ((RiscV.L3.holWordExtract 3 2 0 p).toNat * 8 + j)
    rw [BitVec.getLsbD_append, if_pos sumBound]

/-- Original byte/half/word/double alignment supplies the within-word bound.
No independent range assumption is imposed on a source memory instruction. -/
theorem memory_aligned_access_within (p : BitVec 64) (k : Fin 4)
    (aligned : holAligned k.val p = true) :
    (RiscV.L3.holWordExtract 3 2 0 p).toNat + (2 : Nat) ^ k.val ≤ 8 := by
  have low : (RiscV.L3.holWordExtract 3 2 0 p).toNat = p.toNat % 8 := by
    simp [RiscV.L3.holWordExtract]
  rw [low]
  have alignment := (holAligned_iff k.val p).mp aligned
  have cases : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ k.val = 3 := by omega
  rcases cases with h | h | h | h <;> simp [h] at alignment ⊢ <;> omega

/-- All four source access sizes use the exact within-word raw read slice. -/
theorem memory_raw_read_aligned_size (p : BitVec 64) (s : riscv_state)
    (k : Fin 4) (aligned : holAligned k.val p = true) :
    (rawReadData p s).extractLsb' 0 ((2 : Nat) ^ k.val * 8) =
      (MEM (RiscV.L3.holWordExtract 61 63 3 p) s).extractLsb'
        ((RiscV.L3.holWordExtract 3 2 0 p).toNat * 8) ((2 : Nat) ^ k.val * 8) := by
  exact memory_raw_read_within_word p s ((2 : Nat) ^ k.val)
    (memory_aligned_access_within p k aligned)

/-- Exact partial raw-store word update when the bytes fit within one word.
The source alignment supplies this helper condition in all encoder cases. -/
theorem memory_raw_write_within_word (p v : BitVec 64) (s : riscv_state)
    (n : Nat) (within : (RiscV.L3.holWordExtract 3 2 0 p).toNat + n ≤ 8) :
    rawWriteData (p,v,n) s =
      let mask : BitVec 64 := (BitVec.ofNat 64 1 <<< (n * 8)) - BitVec.ofNat 64 1
      let shift := (RiscV.L3.holWordExtract 3 2 0 p).toNat * 8
      let idx := RiscV.L3.holWordExtract 61 63 3 p
      «write'MEM» ((MEM idx s &&& ~~~(mask <<< shift)) |||
        ((v &&& mask) <<< shift), idx) s := by
  dsimp only [rawWriteData]
  by_cases zero : (RiscV.L3.holWordExtract 3 2 0 p).toNat = 0
  · simp [zero]
  · simp [zero, within]

/-- All original aligned source access sizes use this exact partial-store word. -/
theorem memory_raw_write_aligned_size (p v : BitVec 64) (s : riscv_state)
    (k : Fin 4) (aligned : holAligned k.val p = true) :
    rawWriteData (p,v,(2 : Nat) ^ k.val) s =
      let mask : BitVec 64 := (BitVec.ofNat 64 1 <<< ((2 : Nat) ^ k.val * 8)) - BitVec.ofNat 64 1
      let shift := (RiscV.L3.holWordExtract 3 2 0 p).toNat * 8
      let idx := RiscV.L3.holWordExtract 61 63 3 p
      «write'MEM» ((MEM idx s &&& ~~~(mask <<< shift)) |||
        ((v &&& mask) <<< shift), idx) s := by
  exact memory_raw_write_within_word p v s ((2 : Nat) ^ k.val)
    (memory_aligned_access_within p k aligned)

/-- Native store mask is the low-bit all-ones mask, even at full word width. -/
theorem memory_store_mask (bits : Nat) :
    (BitVec.ofNat 64 1 <<< bits) - BitVec.ofNat 64 1 =
      (BitVec.allOnes bits).setWidth 64 := by
  have shifted : (BitVec.ofNat 64 1 <<< bits) = BitVec.ofNat 64 (2 ^ bits) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  rw [shifted, BitVec.ofNat_sub_ofNat_of_le (2 ^ bits) 1 (by decide)
    (Nat.one_le_two_pow)]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_allOnes]

/-- Exact bit effect of the native partial-store word expression. -/
theorem memory_store_word_bit (old v : BitVec 64) (bits shift j : Nat)
    (hj : j < 64) :
    ((old &&& ~~~(((BitVec.ofNat 64 1 <<< bits) - BitVec.ofNat 64 1) <<< shift)) |||
      ((v &&& ((BitVec.ofNat 64 1 <<< bits) - BitVec.ofNat 64 1)) <<< shift)).getLsbD j =
      if shift ≤ j ∧ j < shift + bits then v.getLsbD (j - shift)
      else old.getLsbD j := by
  rw [memory_store_mask]
  by_cases lower : shift ≤ j
  · by_cases upper : j < shift + bits
    · have selected : j - shift < bits := by omega
      have sub64 : j - shift < 64 := by omega
      simp [lower, upper, selected, sub64, hj, Nat.not_lt.mpr lower]
    · have unselected : ¬j - shift < bits := by omega
      have sub64 : j - shift < 64 := by omega
      simp [lower, upper, unselected, hj, Nat.not_lt.mpr lower]
  · simp [lower, hj, Nat.lt_of_not_ge lower]

/-- Byte effect of the exact native partial-store word expression. -/
theorem memory_store_word_byte (old v : BitVec 64) (offset n : Nat) (i : Fin 8) :
    ((old &&& ~~~(((BitVec.ofNat 64 1 <<< (n * 8)) - BitVec.ofNat 64 1) <<< (offset * 8))) |||
      ((v &&& ((BitVec.ofNat 64 1 <<< (n * 8)) - BitVec.ofNat 64 1)) <<< (offset * 8))).extractLsb' (i.val * 8) 8 =
      if offset ≤ i.val ∧ i.val < offset + n then
        v.extractLsb' ((i.val - offset) * 8) 8
      else old.extractLsb' (i.val * 8) 8 := by
  by_cases selected : offset ≤ i.val ∧ i.val < offset + n
  · rw [if_pos selected]
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have bound : i.val * 8 + j < 64 := by omega
    have region : offset * 8 ≤ i.val * 8 + j ∧ i.val * 8 + j < offset * 8 + n * 8 := by omega
    have difference : i.val * 8 + j - offset * 8 = (i.val - offset) * 8 + j := by omega
    simp only [BitVec.getLsbD_extractLsb']
    rw [memory_store_word_bit old v (n * 8) (offset * 8) (i.val * 8 + j) bound,
      if_pos region, difference]
  · rw [if_neg selected]
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have bound : i.val * 8 + j < 64 := by omega
    have region : ¬(offset * 8 ≤ i.val * 8 + j ∧ i.val * 8 + j < offset * 8 + n * 8) := by omega
    simp only [BitVec.getLsbD_extractLsb']
    rw [memory_store_word_bit old v (n * 8) (offset * 8) (i.val * 8 + j) bound,
      if_neg region]

/-- Actual raw partial-store byte effect at every byte in the native word.
Untouched bytes retain MEM8, rather than being discarded with the word update. -/
theorem memory_raw_write_within_byte (p v : BitVec 64) (s : riscv_state)
    (n : Nat) (within : (RiscV.L3.holWordExtract 3 2 0 p).toNat + n ≤ 8)
    (i : Fin 8) :
    (rawWriteData (p,v,n) s).MEM8
      (((RiscV.L3.holWordExtract 61 63 3 p).setWidth 64 <<< 3) + BitVec.ofNat 64 i.val) =
      if (RiscV.L3.holWordExtract 3 2 0 p).toNat ≤ i.val ∧
          i.val < (RiscV.L3.holWordExtract 3 2 0 p).toNat + n then
        v.extractLsb' ((i.val - (RiscV.L3.holWordExtract 3 2 0 p).toNat) * 8) 8
      else s.MEM8
        (((RiscV.L3.holWordExtract 61 63 3 p).setWidth 64 <<< 3) + BitVec.ofNat 64 i.val) := by
  rw [memory_raw_write_within_word p v s n within]
  dsimp only
  rw [memory_write_word_byte, memory_extract_offset8, memory_store_word_byte]
  by_cases selected : (RiscV.L3.holWordExtract 3 2 0 p).toNat ≤ i.val ∧
      i.val < (RiscV.L3.holWordExtract 3 2 0 p).toNat + n
  · simp only [if_pos selected]
  · rw [if_neg selected, if_neg selected, ← memory_extract_offset8,
      memory_read_word_byte]

/-- Actual partial raw store preserves all bytes outside its native word. -/
theorem memory_raw_write_within_frame (p v : BitVec 64) (s : riscv_state)
    (n : Nat) (within : (RiscV.L3.holWordExtract 3 2 0 p).toNat + n ≤ 8)
    (x : BitVec 64)
    (outside : ∀ i : Nat, i < 8 → x ≠
      ((RiscV.L3.holWordExtract 61 63 3 p).setWidth 64 <<< 3) + BitVec.ofNat 64 i) :
    (rawWriteData (p,v,n) s).MEM8 x = s.MEM8 x := by
  rw [memory_raw_write_within_word p v s n within]
  dsimp only
  apply memory_write_word_frame
  exact outside

/-- Complete outside-written-region frame for the actual partial raw store.
This includes untouched bytes inside the containing word and modular addresses. -/
theorem memory_raw_write_region_frame (p v : BitVec 64) (s : riscv_state)
    (n : Nat) (within : (RiscV.L3.holWordExtract 3 2 0 p).toNat + n ≤ 8)
    (x : BitVec 64) (outside : ∀ j : Nat, j < n → x ≠ p + BitVec.ofNat 64 j) :
    (rawWriteData (p,v,n) s).MEM8 x = s.MEM8 x := by
  classical
  by_cases member : ∃ i : Nat, i < 8 ∧ x =
      ((RiscV.L3.holWordExtract 61 63 3 p).setWidth 64 <<< 3) + BitVec.ofNat 64 i
  · obtain ⟨i, bound, hx⟩ := member
    let index : Fin 8 := ⟨i,bound⟩
    have byte := memory_raw_write_within_byte p v s n within index
    have unselected : ¬((RiscV.L3.holWordExtract 3 2 0 p).toNat ≤ i ∧
        i < (RiscV.L3.holWordExtract 3 2 0 p).toNat + n) := by
      intro selected
      have address : x = p + BitVec.ofNat 64
          (i - (RiscV.L3.holWordExtract 3 2 0 p).toNat) := by
        rw [hx]
        conv => rhs; lhs; rw [← memory_address_decomposition p]
        have low : (RiscV.L3.holWordExtract 3 2 0 p).setWidth 64 =
            BitVec.ofNat 64 (RiscV.L3.holWordExtract 3 2 0 p).toNat := by
          apply BitVec.eq_of_toNat_eq
          simp
        rw [low, BitVec.add_assoc, ← BitVec.ofNat_add]
        congr 2
        omega
      exact outside (i - (RiscV.L3.holWordExtract 3 2 0 p).toNat) (by omega) address
    simp only [index, if_neg unselected] at byte
    rw [← hx] at byte
    exact byte
  · apply memory_raw_write_within_frame p v s n within x
    intro i bound hx
    exact member ⟨i,bound,hx⟩

/-- Every requested byte of an actual within-word store receives the value byte. -/
theorem memory_raw_write_selected_byte (p v : BitVec 64) (s : riscv_state)
    (n : Nat) (within : (RiscV.L3.holWordExtract 3 2 0 p).toNat + n ≤ 8)
    (j : Nat) (selected : j < n) :
    (rawWriteData (p,v,n) s).MEM8 (p + BitVec.ofNat 64 j) =
      v.extractLsb' (j * 8) 8 := by
  let i : Fin 8 := ⟨(RiscV.L3.holWordExtract 3 2 0 p).toNat + j, by omega⟩
  have byte := memory_raw_write_within_byte p v s n within i
  have low : (RiscV.L3.holWordExtract 3 2 0 p).setWidth 64 =
      BitVec.ofNat 64 (RiscV.L3.holWordExtract 3 2 0 p).toNat := by
    apply BitVec.eq_of_toNat_eq
    simp
  have address := congrArg (fun a : BitVec 64 => a + BitVec.ofNat 64 j)
    (memory_address_decomposition p)
  rw [low, BitVec.add_assoc, ← BitVec.ofNat_add] at address
  have region : (RiscV.L3.holWordExtract 3 2 0 p).toNat ≤ i.val ∧
      i.val < (RiscV.L3.holWordExtract 3 2 0 p).toNat + n := by dsimp [i]; omega
  rw [if_pos region] at byte
  dsimp only [i] at byte
  rw [address] at byte
  simpa using byte

/-- Every original aligned access size preserves bytes outside the requested region. -/
theorem memory_raw_write_aligned_frame (p v : BitVec 64) (s : riscv_state)
    (k : Fin 4) (aligned : holAligned k.val p = true) (x : BitVec 64)
    (outside : ∀ j : Nat, j < (2 : Nat) ^ k.val → x ≠ p + BitVec.ofNat 64 j) :
    (rawWriteData (p,v,(2 : Nat) ^ k.val) s).MEM8 x = s.MEM8 x := by
  exact memory_raw_write_region_frame p v s ((2 : Nat) ^ k.val)
    (memory_aligned_access_within p k aligned) x outside

/-- Every selected within-word raw-read byte is its actual addressed MEM8 byte. -/
theorem memory_raw_read_selected_byte (p : BitVec 64) (s : riscv_state)
    (j : Nat) (within : (RiscV.L3.holWordExtract 3 2 0 p).toNat + j < 8) :
    (rawReadData p s).extractLsb' (j * 8) 8 = s.MEM8 (p + BitVec.ofNat 64 j) := by
  let i : Fin 8 := ⟨(RiscV.L3.holWordExtract 3 2 0 p).toNat + j, within⟩
  have byte := memory_read_word_byte (RiscV.L3.holWordExtract 61 63 3 p) s i
  have low : (RiscV.L3.holWordExtract 3 2 0 p).setWidth 64 =
      BitVec.ofNat 64 (RiscV.L3.holWordExtract 3 2 0 p).toNat := by
    apply BitVec.eq_of_toNat_eq
    simp
  have address := congrArg (fun a : BitVec 64 => a + BitVec.ofNat 64 j)
    (memory_address_decomposition p)
  rw [low, BitVec.add_assoc, ← BitVec.ofNat_add] at address
  rw [memory_extract_offset8] at byte
  dsimp only [i] at byte
  rw [address] at byte
  rw [← byte]
  dsimp only [rawReadData]
  by_cases zero : (RiscV.L3.holWordExtract 3 2 0 p).toNat = 0
  · simp [zero]
  · simp only [beq_iff_eq, zero, ↓reduceIte, memory_extract_low64]
    apply BitVec.eq_of_getLsbD_eq
    intro b hb
    have indexBound : (RiscV.L3.holWordExtract 3 2 0 p).toNat * 8 + (j * 8 + b) < 64 := by omega
    have lowBound : j * 8 + b < 64 := by omega
    have highBound : (RiscV.L3.holWordExtract 3 2 0 p).toNat * 8 + (j * 8 + b) < 128 := by omega
    have notHigh : ¬128 ≤ j * 8 + b := by omega
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_sshiftRight]
    simp [hb, lowBound, highBound, notHigh]
    change (MEM (RiscV.L3.holWordExtract 61 63 3 p + 1) s ++
      MEM (RiscV.L3.holWordExtract 61 63 3 p) s).getLsbD
        ((RiscV.L3.holWordExtract 3 2 0 p).toNat * 8 + (j * 8 + b)) =
      (MEM (RiscV.L3.holWordExtract 61 63 3 p) s).getLsbD
        (((RiscV.L3.holWordExtract 3 2 0 p).toNat + j) * 8 + b)
    rw [BitVec.getLsbD_append, if_pos indexBound]
    congr 1
    omega

/-- Byte correspondence for every original aligned source load size. -/
theorem memory_raw_read_aligned_byte (p : BitVec 64) (s : riscv_state)
    (k : Fin 4) (aligned : holAligned k.val p = true)
    (j : Nat) (selected : j < (2 : Nat) ^ k.val) :
    (rawReadData p s).extractLsb' (j * 8) 8 = s.MEM8 (p + BitVec.ofNat 64 j) := by
  have within := memory_aligned_access_within p k aligned
  exact memory_raw_read_selected_byte p s j (by omega)

/-- Byte correspondence for every original aligned source store size. -/
theorem memory_raw_write_aligned_byte (p v : BitVec 64) (s : riscv_state)
    (k : Fin 4) (aligned : holAligned k.val p = true)
    (j : Nat) (selected : j < (2 : Nat) ^ k.val) :
    (rawWriteData (p,v,(2 : Nat) ^ k.val) s).MEM8 (p + BitVec.ofNat 64 j) =
      v.extractLsb' (j * 8) 8 := by
  exact memory_raw_write_selected_byte p v s ((2 : Nat) ^ k.val)
    (memory_aligned_access_within p k aligned) j selected

/-- Exact byte-expanded little-endian native read, using only original alignment. -/
theorem raw_read_expanded1 (p : BitVec 64) (s : riscv_state)
    (aligned : holAligned 0 p = true) :
    (rawReadData p s).extractLsb' 0 8 = s.MEM8 p := by
  have b0 := memory_raw_read_aligned_byte p s ⟨0, by decide⟩ aligned 0 (by decide)
  simp only [Nat.reduceMul, BitVec.add_zero] at b0
  rw [← b0]
  try simp only [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb']

/-- Exact byte-expanded little-endian native read, using only original alignment. -/
theorem raw_read_expanded2 (p : BitVec 64) (s : riscv_state)
    (aligned : holAligned 1 p = true) :
    (rawReadData p s).extractLsb' 0 16 = (s.MEM8 (p + 1#64) ++ s.MEM8 p) := by
  have b0 := memory_raw_read_aligned_byte p s ⟨1, by decide⟩ aligned 0 (by decide)
  have b1 := memory_raw_read_aligned_byte p s ⟨1, by decide⟩ aligned 1 (by decide)
  simp only [Nat.reduceMul, BitVec.add_zero] at b0 b1
  rw [← b0, ← b1]
  try simp only [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb']

/-- Exact byte-expanded little-endian native read, using only original alignment. -/
theorem raw_read_expanded4 (p : BitVec 64) (s : riscv_state)
    (aligned : holAligned 2 p = true) :
    (rawReadData p s).extractLsb' 0 32 = (s.MEM8 (p + 3#64) ++ (s.MEM8 (p + 2#64) ++ (s.MEM8 (p + 1#64) ++ s.MEM8 p))) := by
  have b0 := memory_raw_read_aligned_byte p s ⟨2, by decide⟩ aligned 0 (by decide)
  have b1 := memory_raw_read_aligned_byte p s ⟨2, by decide⟩ aligned 1 (by decide)
  have b2 := memory_raw_read_aligned_byte p s ⟨2, by decide⟩ aligned 2 (by decide)
  have b3 := memory_raw_read_aligned_byte p s ⟨2, by decide⟩ aligned 3 (by decide)
  simp only [Nat.reduceMul, BitVec.add_zero] at b0 b1 b2 b3
  rw [← b0, ← b1, ← b2, ← b3]
  try simp only [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb']

/-- Exact byte-expanded little-endian native read, using only original alignment. -/
theorem raw_read_expanded8 (p : BitVec 64) (s : riscv_state)
    (aligned : holAligned 3 p = true) :
    (rawReadData p s).extractLsb' 0 64 = (s.MEM8 (p + 7#64) ++ (s.MEM8 (p + 6#64) ++ (s.MEM8 (p + 5#64) ++ (s.MEM8 (p + 4#64) ++ (s.MEM8 (p + 3#64) ++ (s.MEM8 (p + 2#64) ++ (s.MEM8 (p + 1#64) ++ s.MEM8 p))))))) := by
  have b0 := memory_raw_read_aligned_byte p s ⟨3, by decide⟩ aligned 0 (by decide)
  have b1 := memory_raw_read_aligned_byte p s ⟨3, by decide⟩ aligned 1 (by decide)
  have b2 := memory_raw_read_aligned_byte p s ⟨3, by decide⟩ aligned 2 (by decide)
  have b3 := memory_raw_read_aligned_byte p s ⟨3, by decide⟩ aligned 3 (by decide)
  have b4 := memory_raw_read_aligned_byte p s ⟨3, by decide⟩ aligned 4 (by decide)
  have b5 := memory_raw_read_aligned_byte p s ⟨3, by decide⟩ aligned 5 (by decide)
  have b6 := memory_raw_read_aligned_byte p s ⟨3, by decide⟩ aligned 6 (by decide)
  have b7 := memory_raw_read_aligned_byte p s ⟨3, by decide⟩ aligned 7 (by decide)
  simp only [Nat.reduceMul, BitVec.add_zero] at b0 b1 b2 b3 b4 b5 b6 b7
  rw [← b0, ← b1, ← b2, ← b3, ← b4, ← b5, ← b6, ← b7]
  try simp only [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb']

/-- Full original byte-update record of an aligned native store. -/
theorem raw_write_expanded1 (p v : BitVec 64) (s : riscv_state)
    (aligned : holAligned 0 p = true) :
    rawWriteData (p,v,1) s = {s with MEM8 := holUpdate (p + 0#64) (v.extractLsb' 0 8) (s.MEM8)} := by
  rw [rawWriteDataPreservesNonMemory]
  congr 1
  funext x
  by_cases h0 : x = p + 0#64
  · rw [h0]
    have byte := memory_raw_write_aligned_byte p v s ⟨0, by decide⟩ aligned 0 (by decide)
    simp only [Nat.reducePow, Nat.reduceMul] at byte
    rw [byte]
    simp only [holUpdate, ite_true]
  · have outside : ∀ j < (2 : Nat) ^ 0, x ≠ p + BitVec.ofNat 64 j := by
      intro j bound
      have cases : j = 0 := by omega
      rcases cases with rfl
      all_goals assumption
    have frame := memory_raw_write_aligned_frame p v s ⟨0, by decide⟩ aligned x outside
    simp only [Nat.reducePow] at frame
    rw [frame]
    simp only [holUpdate, if_neg (Ne.symm h0)]

/-- Full original byte-update record of an aligned native store. -/
theorem raw_write_expanded2 (p v : BitVec 64) (s : riscv_state)
    (aligned : holAligned 1 p = true) :
    rawWriteData (p,v,2) s = {s with MEM8 := holUpdate (p + 1#64) (v.extractLsb' 8 8) (holUpdate (p + 0#64) (v.extractLsb' 0 8) (s.MEM8))} := by
  rw [rawWriteDataPreservesNonMemory]
  congr 1
  funext x
  by_cases h0 : x = p + 0#64
  · rw [h0]
    have d1 : p + 1#64 ≠ p + 0#64 := by
      intro equal
      have equal := (BitVec.add_right_inj p).mp equal
      contradiction
    have byte := memory_raw_write_aligned_byte p v s ⟨1, by decide⟩ aligned 0 (by decide)
    simp only [Nat.reducePow, Nat.reduceMul] at byte
    rw [byte]
    simp only [holUpdate, ite_true, if_neg d1]
  · by_cases h1 : x = p + 1#64
    · rw [h1]
      have byte := memory_raw_write_aligned_byte p v s ⟨1, by decide⟩ aligned 1 (by decide)
      simp only [Nat.reducePow, Nat.reduceMul] at byte
      rw [byte]
      simp only [holUpdate, ite_true]
    · have outside : ∀ j < (2 : Nat) ^ 1, x ≠ p + BitVec.ofNat 64 j := by
        intro j bound
        have cases : j = 0 ∨ j = 1 := by omega
        rcases cases with rfl | rfl
        all_goals assumption
      have frame := memory_raw_write_aligned_frame p v s ⟨1, by decide⟩ aligned x outside
      simp only [Nat.reducePow] at frame
      rw [frame]
      simp only [holUpdate, if_neg (Ne.symm h0), if_neg (Ne.symm h1)]

/-- Full original byte-update record of an aligned native store. -/
theorem raw_write_expanded4 (p v : BitVec 64) (s : riscv_state)
    (aligned : holAligned 2 p = true) :
    rawWriteData (p,v,4) s = {s with MEM8 := holUpdate (p + 3#64) (v.extractLsb' 24 8) (holUpdate (p + 2#64) (v.extractLsb' 16 8) (holUpdate (p + 1#64) (v.extractLsb' 8 8) (holUpdate (p + 0#64) (v.extractLsb' 0 8) (s.MEM8))))} := by
  rw [rawWriteDataPreservesNonMemory]
  congr 1
  funext x
  by_cases h0 : x = p + 0#64
  · rw [h0]
    have d1 : p + 1#64 ≠ p + 0#64 := by
      intro equal
      have equal := (BitVec.add_right_inj p).mp equal
      contradiction
    have d2 : p + 2#64 ≠ p + 0#64 := by
      intro equal
      have equal := (BitVec.add_right_inj p).mp equal
      contradiction
    have d3 : p + 3#64 ≠ p + 0#64 := by
      intro equal
      have equal := (BitVec.add_right_inj p).mp equal
      contradiction
    have byte := memory_raw_write_aligned_byte p v s ⟨2, by decide⟩ aligned 0 (by decide)
    simp only [Nat.reducePow, Nat.reduceMul] at byte
    rw [byte]
    simp only [holUpdate, ite_true, if_neg d1, if_neg d2, if_neg d3]
  · by_cases h1 : x = p + 1#64
    · rw [h1]
      have d2 : p + 2#64 ≠ p + 1#64 := by
        intro equal
        have equal := (BitVec.add_right_inj p).mp equal
        contradiction
      have d3 : p + 3#64 ≠ p + 1#64 := by
        intro equal
        have equal := (BitVec.add_right_inj p).mp equal
        contradiction
      have byte := memory_raw_write_aligned_byte p v s ⟨2, by decide⟩ aligned 1 (by decide)
      simp only [Nat.reducePow, Nat.reduceMul] at byte
      rw [byte]
      simp only [holUpdate, ite_true, if_neg d2, if_neg d3]
    · by_cases h2 : x = p + 2#64
      · rw [h2]
        have d3 : p + 3#64 ≠ p + 2#64 := by
          intro equal
          have equal := (BitVec.add_right_inj p).mp equal
          contradiction
        have byte := memory_raw_write_aligned_byte p v s ⟨2, by decide⟩ aligned 2 (by decide)
        simp only [Nat.reducePow, Nat.reduceMul] at byte
        rw [byte]
        simp only [holUpdate, ite_true, if_neg d3]
      · by_cases h3 : x = p + 3#64
        · rw [h3]
          have byte := memory_raw_write_aligned_byte p v s ⟨2, by decide⟩ aligned 3 (by decide)
          simp only [Nat.reducePow, Nat.reduceMul] at byte
          rw [byte]
          simp only [holUpdate, ite_true]
        · have outside : ∀ j < (2 : Nat) ^ 2, x ≠ p + BitVec.ofNat 64 j := by
            intro j bound
            have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
            rcases cases with rfl | rfl | rfl | rfl
            all_goals assumption
          have frame := memory_raw_write_aligned_frame p v s ⟨2, by decide⟩ aligned x outside
          simp only [Nat.reducePow] at frame
          rw [frame]
          simp only [holUpdate, if_neg (Ne.symm h0), if_neg (Ne.symm h1), if_neg (Ne.symm h2), if_neg (Ne.symm h3)]

/-- Full original byte-update record of an aligned native store. -/
theorem raw_write_expanded8 (p v : BitVec 64) (s : riscv_state)
    (aligned : holAligned 3 p = true) :
    rawWriteData (p,v,8) s = {s with MEM8 := holUpdate (p + 7#64) (v.extractLsb' 56 8) (holUpdate (p + 6#64) (v.extractLsb' 48 8) (holUpdate (p + 5#64) (v.extractLsb' 40 8) (holUpdate (p + 4#64) (v.extractLsb' 32 8) (holUpdate (p + 3#64) (v.extractLsb' 24 8) (holUpdate (p + 2#64) (v.extractLsb' 16 8) (holUpdate (p + 1#64) (v.extractLsb' 8 8) (holUpdate (p + 0#64) (v.extractLsb' 0 8) (s.MEM8))))))))} := by
  rw [rawWriteDataPreservesNonMemory]
  congr 1
  funext x
  by_cases h0 : x = p + 0#64
  · rw [h0]
    have d1 : p + 1#64 ≠ p + 0#64 := by
      intro equal
      have equal := (BitVec.add_right_inj p).mp equal
      contradiction
    have d2 : p + 2#64 ≠ p + 0#64 := by
      intro equal
      have equal := (BitVec.add_right_inj p).mp equal
      contradiction
    have d3 : p + 3#64 ≠ p + 0#64 := by
      intro equal
      have equal := (BitVec.add_right_inj p).mp equal
      contradiction
    have d4 : p + 4#64 ≠ p + 0#64 := by
      intro equal
      have equal := (BitVec.add_right_inj p).mp equal
      contradiction
    have d5 : p + 5#64 ≠ p + 0#64 := by
      intro equal
      have equal := (BitVec.add_right_inj p).mp equal
      contradiction
    have d6 : p + 6#64 ≠ p + 0#64 := by
      intro equal
      have equal := (BitVec.add_right_inj p).mp equal
      contradiction
    have d7 : p + 7#64 ≠ p + 0#64 := by
      intro equal
      have equal := (BitVec.add_right_inj p).mp equal
      contradiction
    have byte := memory_raw_write_aligned_byte p v s ⟨3, by decide⟩ aligned 0 (by decide)
    simp only [Nat.reducePow, Nat.reduceMul] at byte
    rw [byte]
    simp only [holUpdate, ite_true, if_neg d1, if_neg d2, if_neg d3, if_neg d4, if_neg d5, if_neg d6, if_neg d7]
  · by_cases h1 : x = p + 1#64
    · rw [h1]
      have d2 : p + 2#64 ≠ p + 1#64 := by
        intro equal
        have equal := (BitVec.add_right_inj p).mp equal
        contradiction
      have d3 : p + 3#64 ≠ p + 1#64 := by
        intro equal
        have equal := (BitVec.add_right_inj p).mp equal
        contradiction
      have d4 : p + 4#64 ≠ p + 1#64 := by
        intro equal
        have equal := (BitVec.add_right_inj p).mp equal
        contradiction
      have d5 : p + 5#64 ≠ p + 1#64 := by
        intro equal
        have equal := (BitVec.add_right_inj p).mp equal
        contradiction
      have d6 : p + 6#64 ≠ p + 1#64 := by
        intro equal
        have equal := (BitVec.add_right_inj p).mp equal
        contradiction
      have d7 : p + 7#64 ≠ p + 1#64 := by
        intro equal
        have equal := (BitVec.add_right_inj p).mp equal
        contradiction
      have byte := memory_raw_write_aligned_byte p v s ⟨3, by decide⟩ aligned 1 (by decide)
      simp only [Nat.reducePow, Nat.reduceMul] at byte
      rw [byte]
      simp only [holUpdate, ite_true, if_neg d2, if_neg d3, if_neg d4, if_neg d5, if_neg d6, if_neg d7]
    · by_cases h2 : x = p + 2#64
      · rw [h2]
        have d3 : p + 3#64 ≠ p + 2#64 := by
          intro equal
          have equal := (BitVec.add_right_inj p).mp equal
          contradiction
        have d4 : p + 4#64 ≠ p + 2#64 := by
          intro equal
          have equal := (BitVec.add_right_inj p).mp equal
          contradiction
        have d5 : p + 5#64 ≠ p + 2#64 := by
          intro equal
          have equal := (BitVec.add_right_inj p).mp equal
          contradiction
        have d6 : p + 6#64 ≠ p + 2#64 := by
          intro equal
          have equal := (BitVec.add_right_inj p).mp equal
          contradiction
        have d7 : p + 7#64 ≠ p + 2#64 := by
          intro equal
          have equal := (BitVec.add_right_inj p).mp equal
          contradiction
        have byte := memory_raw_write_aligned_byte p v s ⟨3, by decide⟩ aligned 2 (by decide)
        simp only [Nat.reducePow, Nat.reduceMul] at byte
        rw [byte]
        simp only [holUpdate, ite_true, if_neg d3, if_neg d4, if_neg d5, if_neg d6, if_neg d7]
      · by_cases h3 : x = p + 3#64
        · rw [h3]
          have d4 : p + 4#64 ≠ p + 3#64 := by
            intro equal
            have equal := (BitVec.add_right_inj p).mp equal
            contradiction
          have d5 : p + 5#64 ≠ p + 3#64 := by
            intro equal
            have equal := (BitVec.add_right_inj p).mp equal
            contradiction
          have d6 : p + 6#64 ≠ p + 3#64 := by
            intro equal
            have equal := (BitVec.add_right_inj p).mp equal
            contradiction
          have d7 : p + 7#64 ≠ p + 3#64 := by
            intro equal
            have equal := (BitVec.add_right_inj p).mp equal
            contradiction
          have byte := memory_raw_write_aligned_byte p v s ⟨3, by decide⟩ aligned 3 (by decide)
          simp only [Nat.reducePow, Nat.reduceMul] at byte
          rw [byte]
          simp only [holUpdate, ite_true, if_neg d4, if_neg d5, if_neg d6, if_neg d7]
        · by_cases h4 : x = p + 4#64
          · rw [h4]
            have d5 : p + 5#64 ≠ p + 4#64 := by
              intro equal
              have equal := (BitVec.add_right_inj p).mp equal
              contradiction
            have d6 : p + 6#64 ≠ p + 4#64 := by
              intro equal
              have equal := (BitVec.add_right_inj p).mp equal
              contradiction
            have d7 : p + 7#64 ≠ p + 4#64 := by
              intro equal
              have equal := (BitVec.add_right_inj p).mp equal
              contradiction
            have byte := memory_raw_write_aligned_byte p v s ⟨3, by decide⟩ aligned 4 (by decide)
            simp only [Nat.reducePow, Nat.reduceMul] at byte
            rw [byte]
            simp only [holUpdate, ite_true, if_neg d5, if_neg d6, if_neg d7]
          · by_cases h5 : x = p + 5#64
            · rw [h5]
              have d6 : p + 6#64 ≠ p + 5#64 := by
                intro equal
                have equal := (BitVec.add_right_inj p).mp equal
                contradiction
              have d7 : p + 7#64 ≠ p + 5#64 := by
                intro equal
                have equal := (BitVec.add_right_inj p).mp equal
                contradiction
              have byte := memory_raw_write_aligned_byte p v s ⟨3, by decide⟩ aligned 5 (by decide)
              simp only [Nat.reducePow, Nat.reduceMul] at byte
              rw [byte]
              simp only [holUpdate, ite_true, if_neg d6, if_neg d7]
            · by_cases h6 : x = p + 6#64
              · rw [h6]
                have d7 : p + 7#64 ≠ p + 6#64 := by
                  intro equal
                  have equal := (BitVec.add_right_inj p).mp equal
                  contradiction
                have byte := memory_raw_write_aligned_byte p v s ⟨3, by decide⟩ aligned 6 (by decide)
                simp only [Nat.reducePow, Nat.reduceMul] at byte
                rw [byte]
                simp only [holUpdate, ite_true, if_neg d7]
              · by_cases h7 : x = p + 7#64
                · rw [h7]
                  have byte := memory_raw_write_aligned_byte p v s ⟨3, by decide⟩ aligned 7 (by decide)
                  simp only [Nat.reducePow, Nat.reduceMul] at byte
                  rw [byte]
                  simp only [holUpdate, ite_true]
                · have outside : ∀ j < (2 : Nat) ^ 3, x ≠ p + BitVec.ofNat 64 j := by
                    intro j bound
                    have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
                    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
                    all_goals assumption
                  have frame := memory_raw_write_aligned_frame p v s ⟨3, by decide⟩ aligned x outside
                  simp only [Nat.reducePow] at frame
                  rw [frame]
                  simp only [holUpdate, if_neg (Ne.symm h0), if_neg (Ne.symm h1), if_neg (Ne.symm h2), if_neg (Ne.symm h3), if_neg (Ne.symm h4), if_neg (Ne.symm h5), if_neg (Ne.symm h6), if_neg (Ne.symm h7)]

end Flapjack.RiscV.L3.Step.ByteMemory
