import Flapjack.RiscV.CorrectnessEncoding.MemorySource
import Flapjack.RiscV.CorrectnessEncoding.MemoryBytes

/-! Literal source read-value reconstruction for native Mem correctness.
These are untagged composition facts with no separately named HOL originals.
Source assertions are preserved in the executed readMemWord; value extraction
is valid even when they fail. No successful native run or postrelation is assumed. -/
namespace Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
set_option autoImplicit false

/-- Literal value recursion of original read_mem_word, independent of its
assertion-state component. This does not replace the reviewed evaluator. -/
def sourceReadWord {width resultWidth : Nat} (be : Bool)
    (mem : BitVec width → BitVec 8) (p : BitVec width) : Nat → BitVec resultWidth
  | 0 => 0
  | n + 1 => (sourceReadWord be mem (if be then p - 1 else p + 1) n <<< (8 : Nat)) |||
      (mem p).setWidth resultWidth

/-- Full source read value equation, independent positive word dimensions,
arbitrary byte counts, both endian branches and failed assertions retained.
Untagged consequence, not a separately named HOL theorem or narrowed port. -/
theorem source_read_word_value {width resultWidth : Nat} [NeZero width] [NeZero resultWidth]
    (p : BitVec width) (n : Nat) (s : AsmState width) :
    (readMemWord (resultWidth := resultWidth) p n s).1 =
      sourceReadWord s.be s.mem p n := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    rw [readMemWord_succ]
    dsimp only
    have mem := readMemWord_mem_eq_direct (resultWidth := resultWidth)
      (if s.be then p - 1 else p + 1) n s
    simp only [readMem, mem, ih, sourceReadWord]

/-- Every bit of the literal little-endian source read, including zero padding
and arbitrary byte counts. Addresses retain modular addition. Untagged local
infrastructure, not a separately named HOL theorem. -/
theorem source_read_word_bit (mem : BitVec 64 → BitVec 8) (p : BitVec 64)
    (n j : Nat) (bound : j < 64) :
    (sourceReadWord (resultWidth := 64) false mem p n).getLsbD j =
      if j < n * 8 then (mem (p + BitVec.ofNat 64 (j / 8))).getLsbD (j % 8) else false := by
  induction n generalizing p j with
  | zero => simp [sourceReadWord]
  | succ n ih =>
    simp only [sourceReadWord, Bool.false_eq_true, reduceIte,
      BitVec.getLsbD_or, BitVec.getLsbD_setWidth]
    rw [BitVec.getLsbD_shiftLeft]
    by_cases low : j < 8
    · have div : j / 8 = 0 := by omega
      have mod : j % 8 = j := by omega
      have selected : j < (n + 1) * 8 := by omega
      simp [bound, low, div, mod, selected]
    · have tailBound : j - 8 < 64 := by omega
      have byte : (mem p).getLsbD j = false := BitVec.getLsbD_of_ge _ _ (by omega)
      simp only [bound, low, decide_true, decide_false, Bool.not_false,
        Bool.true_and, byte, Bool.or_false]
      rw [ih (p + 1) (j - 8) tailBound]
      have range : j - 8 < n * 8 ↔ j < (n + 1) * 8 := by omega
      have div : j / 8 = (j - 8) / 8 + 1 := by omega
      have mod : (j - 8) % 8 = j % 8 := by omega
      have address : (p + 1) + BitVec.ofNat 64 ((j - 8) / 8) =
          p + BitVec.ofNat 64 (j / 8) := by
        rw [div, show (j - 8) / 8 + 1 = 1 + (j - 8) / 8 by omega,
          BitVec.ofNat_add]
        exact BitVec.add_assoc _ _ _
      simp only [range, mod, address]

/-- Each selected bit of the native within-word raw read belongs to the
addressed byte. The region condition is derived from source alignment by the
size wrapper below; this is not an extra full encoder hypothesis. -/
theorem native_raw_read_bit (p : BitVec 64) (t : riscv_state) (n j : Nat)
    (within : (RiscV.L3.holWordExtract 3 2 0 p).toNat + n ≤ 8)
    (selected : j < n * 8) :
    (rawReadData p t).getLsbD j =
      (t.MEM8 (p + BitVec.ofNat 64 (j / 8))).getLsbD (j % 8) := by
  let offset := (RiscV.L3.holWordExtract 3 2 0 p).toNat
  have indexBound : offset + j / 8 < 8 := by dsimp [offset]; omega
  let index : Fin 8 := ⟨offset + j / 8, indexBound⟩
  have bytes := memory_read_word_byte (RiscV.L3.holWordExtract 61 63 3 p) t index
  have address :
      ((RiscV.L3.holWordExtract 61 63 3 p).setWidth 64 <<< 3) +
          BitVec.ofNat 64 index.val = p + BitVec.ofNat 64 (j / 8) := by
    dsimp [index]
    rw [BitVec.ofNat_add, ← BitVec.add_assoc]
    have offsetWord : BitVec.ofNat 64 offset =
        (RiscV.L3.holWordExtract 3 2 0 p).setWidth 64 := by
      apply BitVec.eq_of_toNat_eq
      simp [offset]
    rw [offsetWord]
    simpa [RiscV.bitVecWordShiftLeft] using
      congrArg (fun a : BitVec 64 => a + BitVec.ofNat 64 (j / 8))
        (memory_address_decomposition p)
  rw [address] at bytes
  have indexSize : index.val * 8 + 7 + 1 - index.val * 8 = 8 := by omega
  have extract (w : BitVec 64) :
      RiscV.L3.holWordExtract 8 (index.val * 8 + 7) (index.val * 8) w =
        w.extractLsb' (index.val * 8) 8 := by
    apply BitVec.eq_of_toNat_eq
    have upper : index.val * 8 + 7 ≤ 63 := by have := index.isLt; omega
    simp [RiscV.L3.holWordExtract, BitVec.extractLsb'_toNat,
      Nat.min_eq_left upper, indexSize]
  rw [extract] at bytes
  have byteBit := congrArg (fun w : BitVec 8 => w.getLsbD (j % 8)) bytes
  simp only [BitVec.getLsbD_extractLsb'] at byteBit
  have modBound : j % 8 < 8 := Nat.mod_lt _ (by decide)
  simp only [modBound, decide_true, Bool.true_and] at byteBit
  have slice := congrArg (fun w => w.getLsbD j) (memory_raw_read_within_word p t n within)
  simp only [BitVec.getLsbD_extractLsb', selected, decide_true, Bool.true_and, Nat.zero_add] at slice
  rw [slice]
  rw [← byteBit]
  congr 1
  dsimp [index, offset]
  omega

/-- Native truncation agrees with the literal source value when corresponding
bytes agree. No target-run or post-state relation is assumed. The selected-byte
premise is an initial-memory fact discharged from the original source domain
and initial target state relation in encoder assembly. -/
theorem source_read_native_value (p : BitVec 64) (s : AsmState 64)
    (t : riscv_state) (k : Fin 4) (little : s.be = false)
    (aligned : holAligned k.val p = true)
    (bytes : ∀ j < (2 : Nat) ^ k.val,
      s.mem (p + BitVec.ofNat 64 j) = t.MEM8 (p + BitVec.ofNat 64 j)) :
    (readMemWord (resultWidth := 64) p ((2 : Nat) ^ k.val) s).1 =
      ((rawReadData p t).extractLsb' 0 ((2 : Nat) ^ k.val * 8)).setWidth 64 := by
  rw [source_read_word_value, little]
  apply BitVec.eq_of_getLsbD_eq
  intro j bound
  rw [source_read_word_bit _ _ _ _ bound]
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', bound,
    decide_true, Bool.true_and, Nat.zero_add]
  by_cases selected : j < (2 : Nat) ^ k.val * 8
  · have byteBound : j / 8 < (2 : Nat) ^ k.val := by omega
    rw [if_pos selected, bytes _ byteBound]
    rw [native_raw_read_bit p t ((2 : Nat) ^ k.val) j
      (memory_aligned_access_within p k aligned) selected]
    simp [selected]
  · simp [selected]

/-- Initial native/source memory agreement and the actual source read's
success supply every selected byte; no separate byte-agreement assumption or
native execution premise survives this composition. Untagged helper for Mem. -/
theorem source_read_native_initial (p : BitVec 64) (s : AsmState 64)
    (t : riscv_state) (k : Fin 4) (little : s.be = false)
    (aligned : holAligned k.val p = true)
    (success : (readMemWord (resultWidth := 64) p ((2 : Nat) ^ k.val) s).2.failed = false)
    (relation : targetStateRel Compiler.Encoders.RiscV.Target.riscvTarget s t) :
    (readMemWord (resultWidth := 64) p ((2 : Nat) ^ k.val) s).1 =
      ((rawReadData p t).extractLsb' 0 ((2 : Nat) ^ k.val * 8)).setWidth 64 := by
  apply source_read_native_value p s t k little aligned
  intro j bound
  have domain := source_read_domain p ((2 : Nat) ^ k.val) s little success j bound
  have memory := relation.2.2.1 (p + BitVec.ofNat 64 j) domain
  exact memory.symm

/-- All four literal source memLoad values agree with native raw-read
truncation. The source operation's own success discharges original alignment
and the full byte domain, using only the initial target relation and endian
fact. No native run or desired postrelation is assumed. Untagged composition,
not the assembled original full Mem encoder theorem. -/
theorem source_memload_native_value (r : Nat) (address : HolAddr 64)
    (s : AsmState 64) (t : riscv_state) (k : Fin 4) (little : s.be = false)
    (success : (memLoad ((2 : Nat) ^ k.val) r address s).failed = false)
    (relation : targetStateRel Compiler.Encoders.RiscV.Target.riscvTarget s t) :
    (memLoad ((2 : Nat) ^ k.val) r address s).regs r =
      ((rawReadData (addrHOL address s) t).extractLsb' 0 ((2 : Nat) ^ k.val * 8)).setWidth 64 := by
  have guards := (source_memload_success ((2 : Nat) ^ k.val) r address s).mp success
  have log : holLOG2 ((2 : Nat) ^ k.val) = k.val := by
    have cases : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ k.val = 3 := by have := k.isLt; omega
    rcases cases with h | h | h | h <;> simp [h, holLOG2_eq_log2]
  have aligned : holAligned k.val (addrHOL address s) = true := by
    simpa only [log] using guards.2.2
  have footprint := guards.2.1
  simp only [little, Bool.false_eq_true, reduceIte] at footprint
  have readSuccess :
      (readMemWord (resultWidth := 64) (addrHOL address s) ((2 : Nat) ^ k.val) s).2.failed = false :=
    (source_read_success _ _ s).mpr ⟨guards.1, by simpa only [little] using footprint⟩
  have value := source_read_native_initial (addrHOL address s) s t k little aligned readSuccess relation
  simpa [memLoad, little, updReg, assertState] using value


/-- Concrete source values matching the original source/native oracle fixtures.
These kernel regressions have no independently named HOL originals. -/
private def readFixtureMem (p : BitVec 64) : BitVec 8 := (p + 128).setWidth 8

theorem read1_zero : sourceReadWord (resultWidth := 64) false readFixtureMem (0 : BitVec 64) 1 = 128 := by decide

theorem read1_wrap : sourceReadWord (resultWidth := 64) false readFixtureMem (18446744073709551615 : BitVec 64) 1 = 127 := by decide

theorem read2_zero : sourceReadWord (resultWidth := 64) false readFixtureMem (0 : BitVec 64) 2 = 33152 := by decide

theorem read2_wrap : sourceReadWord (resultWidth := 64) false readFixtureMem (18446744073709551614 : BitVec 64) 2 = 32638 := by decide

theorem read4_zero : sourceReadWord (resultWidth := 64) false readFixtureMem (0 : BitVec 64) 4 = 2206368128 := by decide

theorem read4_wrap : sourceReadWord (resultWidth := 64) false readFixtureMem (18446744073709551612 : BitVec 64) 4 = 2138996092 := by decide

theorem read8_zero : sourceReadWord (resultWidth := 64) false readFixtureMem (0 : BitVec 64) 8 = 9765639646188044672 := by decide

theorem read8_wrap : sourceReadWord (resultWidth := 64) false readFixtureMem (18446744073709551608 : BitVec 64) 8 = 9186918263483431288 := by decide

end Flapjack.RiscV.TargetProof
