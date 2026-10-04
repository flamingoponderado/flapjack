import Flapjack.RiscV.CorrectnessEncoding.MemorySource
import Flapjack.RiscV.CorrectnessEncoding.MemoryBytes
import Flapjack.Compiler.Backend.LabToTarget.InstMem

/-! Source/native store post-memory consequences for the original Mem case.
These compositions have no separately named HOL originals and remain untagged.
Original source assertions and independent positive word widths are retained;
no native execution or desired post-state relation is assumed. -/
namespace Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
open Compiler.Backend.LabToTarget
set_option autoImplicit false

/-- Complete source memory equation, even on failed domain assertions.
The pure helper characterizes the reviewed writer; it does not replace it. -/
theorem source_write_word_memory {width valueWidth : Nat} [NeZero width] [NeZero valueWidth]
    (p : BitVec width) (n : Nat) (v : BitVec valueWidth) (s : AsmState width) :
    (writeMemWord p n v s).mem = wmwMem s.be s.mem p n v := by
  rw [writeMemWord_eq]
  rfl

/-- The literal pure source writer's selected value byte. Unlike the existing
LabToTarget specialization, the value width has no lower-bound restriction. -/
private theorem source_write_value_at {width valueWidth : Nat} [NeZero width]
    (be : Bool) (mem : BitVec width → BitVec 8) (p : BitVec width) (n : Nat)
    (v : BitVec valueWidth) (j : Nat) (selected : j < n) (unique : n ≤ 2 ^ width) :
    wmwMem be mem p n v (stepAddr be p j) = (v >>> (8 * j)).setWidth 8 := by
  induction n generalizing p v j with
  | zero => omega
  | succ n ih =>
    simp only [wmwMem]
    cases j with
    | zero => simp [stepAddr_zero]
    | succ j =>
      have different : stepAddr be p (j + 1) ≠ p := by
        have bound : j + 1 < 2 ^ width := by omega
        intro equality
        have value : BitVec.ofNat width (j + 1) = 0 := by
          cases be <;> simp only [stepAddr, Bool.false_eq_true, reduceIte] at equality
          · linear_combination equality
          · linear_combination -equality
        have numeric := congrArg BitVec.toNat value
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] at numeric
        simp at numeric
      rw [if_neg different, ← stepAddr_succ, ih _ _ j (by omega) (by omega)]
      apply BitVec.eq_of_getLsbD_eq
      intro i bound
      simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
        bound, decide_true, Bool.true_and]
      congr 1
      omega

/-- Every byte of the literal little-endian source write, for independently
sized values. The count bound only excludes revisiting an address after a full
modular cycle, and is automatically discharged for all four RV64 store sizes. -/
theorem source_write_selected_byte {width valueWidth : Nat} [NeZero width] [NeZero valueWidth]
    (p : BitVec width) (n : Nat) (v : BitVec valueWidth) (s : AsmState width)
    (little : s.be = false) (j : Nat) (selected : j < n) (unique : n ≤ 2 ^ width) :
    (writeMemWord p n v s).mem (p + BitVec.ofNat width j) =
      (v >>> (8 * j)).setWidth 8 := by
  rw [source_write_word_memory, little]
  simpa only [stepAddr, Bool.false_eq_true, reduceIte] using
    source_write_value_at false s.mem p n v j selected unique

/-- The source write leaves every unvisited byte unchanged, including writes
whose original assertions fail. Counts and independent widths stay arbitrary. -/
theorem source_write_region_frame {width valueWidth : Nat} [NeZero width] [NeZero valueWidth]
    (p : BitVec width) (n : Nat) (v : BitVec valueWidth) (s : AsmState width)
    (little : s.be = false) (x : BitVec width)
    (outside : ∀ j < n, x ≠ p + BitVec.ofNat width j) :
    (writeMemWord p n v s).mem x = s.mem x := by
  rw [source_write_word_memory, little]
  apply wmwMem_other
  simpa only [stepAddr, Bool.false_eq_true, reduceIte] using outside

/-- Initial memory agreement survives all four source/native store sizes on
the entire original source domain. Selected bytes agree by literal value
extraction; every other byte agrees by both actual outside-region frames.
No successful native execution or desired postrelation is a premise. -/
theorem source_write_native_memory (p v : BitVec 64) (s : AsmState 64)
    (t : riscv_state) (k : Fin 4) (little : s.be = false)
    (aligned : holAligned k.val p = true)
    (relation : targetStateRel Compiler.Encoders.RiscV.Target.riscvTarget s t) :
    ∀ x, s.memDomain x →
      (writeMemWord p ((2 : Nat) ^ k.val) v s).mem x =
        (rawWriteData (p,v,(2 : Nat) ^ k.val) t).MEM8 x := by
  classical
  intro x domain
  by_cases selected : ∃ j, j < (2 : Nat) ^ k.val ∧ x = p + BitVec.ofNat 64 j
  · obtain ⟨j,bound,address⟩ := selected
    rw [address]
    have count : (2 : Nat) ^ k.val ≤ 2 ^ 64 := by
      exact Nat.pow_le_pow_right (by decide) (by have := k.isLt; omega)
    rw [source_write_selected_byte p ((2 : Nat) ^ k.val) v s little j bound count,
      memory_raw_write_selected_byte p v t ((2 : Nat) ^ k.val)
        (memory_aligned_access_within p k aligned) j bound]
    apply BitVec.eq_of_getLsbD_eq
    intro i bitBound
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_extractLsb', bitBound, decide_true, Bool.true_and]
    congr 1
    omega
  · have outside : ∀ j < (2 : Nat) ^ k.val, x ≠ p + BitVec.ofNat 64 j := by
      intro j bound equality
      exact selected ⟨j,bound,equality⟩
    rw [source_write_region_frame p ((2 : Nat) ^ k.val) v s little x outside,
      memory_raw_write_aligned_frame p v t k aligned x outside]
    exact (relation.2.2.1 x domain).symm

/-- Source stores preserve all fields other than memory and the original
failure flag, at arbitrary counts/endian/address/value. This is a literal
record consequence, not a separately named HOL theorem. -/
theorem source_memstore_frame {width : Nat} [NeZero width]
    (n r : Nat) (address : HolAddr width) (s : AsmState width) :
    (memStore n r address s).memDomain = s.memDomain ∧
    (memStore n r address s).regs = s.regs ∧
    (memStore n r address s).fpRegs = s.fpRegs ∧
    (memStore n r address s).pc = s.pc ∧
    (memStore n r address s).lr = s.lr ∧
    (memStore n r address s).be = s.be ∧
    (memStore n r address s).align = s.align := by
  simp [memStore, writeMemWord_eq, assertState]

/-- Original memStore success supplies its own LOG2 alignment guard; its
post-memory therefore matches the literal native raw store on the original
source domain. Register/address correspondence to the encoded instruction is
still an obligation of the full Mem case, not a premise on this helper. -/
theorem source_memstore_native_memory (r : Nat) (address : HolAddr 64)
    (s : AsmState 64) (t : riscv_state) (k : Fin 4) (little : s.be = false)
    (success : (memStore ((2 : Nat) ^ k.val) r address s).failed = false)
    (relation : targetStateRel Compiler.Encoders.RiscV.Target.riscvTarget s t) :
    ∀ x, (memStore ((2 : Nat) ^ k.val) r address s).memDomain x →
      (memStore ((2 : Nat) ^ k.val) r address s).mem x =
        (rawWriteData (addrHOL address s, readReg r s, (2 : Nat) ^ k.val) t).MEM8 x := by
  have guards := (source_memstore_success ((2 : Nat) ^ k.val) r address s).mp success
  have log : holLOG2 ((2 : Nat) ^ k.val) = k.val := by
    have cases : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ k.val = 3 := by have := k.isLt; omega
    rcases cases with h | h | h | h <;> simp [h, holLOG2_eq_log2]
  have aligned : holAligned k.val (addrHOL address s) = true := by
    simpa only [log] using guards.2.2
  intro x domain
  rw [(source_memstore_frame ((2 : Nat) ^ k.val) r address s).1] at domain
  simpa only [memStore, little, Bool.false_eq_true, reduceIte, assertState_mem] using
    source_write_native_memory (addrHOL address s) (readReg r s) s t k little aligned relation x domain

/-- Source-side values of the matched original paired store fixtures. These
concrete kernel observations are regression infrastructure, not HOL ports. -/
private def storeFixtureMem (p : BitVec 64) : BitVec 8 := (p + 128).setWidth 8

theorem store1_zero :
    (wmwMem false storeFixtureMem (0 : BitVec 64) 1 (9833440827789222417 : BitVec 64)) 0 = 17 ∧
    (wmwMem false storeFixtureMem (0 : BitVec 64) 1 (9833440827789222417 : BitVec 64)) 18446744073709551615 = 127 ∧
    (wmwMem false storeFixtureMem (0 : BitVec 64) 1 (9833440827789222417 : BitVec 64)) 1 = 129 ∧
    (wmwMem false storeFixtureMem (0 : BitVec 64) 1 (9833440827789222417 : BitVec 64)) 42 = 170 := by decide

theorem store1_wrap :
    (wmwMem false storeFixtureMem (18446744073709551615 : BitVec 64) 1 (9833440827789222417 : BitVec 64)) 18446744073709551615 = 17 ∧
    (wmwMem false storeFixtureMem (18446744073709551615 : BitVec 64) 1 (9833440827789222417 : BitVec 64)) 18446744073709551614 = 126 ∧
    (wmwMem false storeFixtureMem (18446744073709551615 : BitVec 64) 1 (9833440827789222417 : BitVec 64)) 0 = 128 ∧
    (wmwMem false storeFixtureMem (18446744073709551615 : BitVec 64) 1 (9833440827789222417 : BitVec 64)) 42 = 170 := by decide

theorem store2_zero :
    (wmwMem false storeFixtureMem (0 : BitVec 64) 2 (9833440827789222417 : BitVec 64)) 0 = 17 ∧
    (wmwMem false storeFixtureMem (0 : BitVec 64) 2 (9833440827789222417 : BitVec 64)) 1 = 34 ∧
    (wmwMem false storeFixtureMem (0 : BitVec 64) 2 (9833440827789222417 : BitVec 64)) 18446744073709551615 = 127 ∧
    (wmwMem false storeFixtureMem (0 : BitVec 64) 2 (9833440827789222417 : BitVec 64)) 2 = 130 ∧
    (wmwMem false storeFixtureMem (0 : BitVec 64) 2 (9833440827789222417 : BitVec 64)) 42 = 170 := by decide

theorem store2_wrap :
    (wmwMem false storeFixtureMem (18446744073709551614 : BitVec 64) 2 (9833440827789222417 : BitVec 64)) 18446744073709551614 = 17 ∧
    (wmwMem false storeFixtureMem (18446744073709551614 : BitVec 64) 2 (9833440827789222417 : BitVec 64)) 18446744073709551615 = 34 ∧
    (wmwMem false storeFixtureMem (18446744073709551614 : BitVec 64) 2 (9833440827789222417 : BitVec 64)) 18446744073709551613 = 125 ∧
    (wmwMem false storeFixtureMem (18446744073709551614 : BitVec 64) 2 (9833440827789222417 : BitVec 64)) 0 = 128 ∧
    (wmwMem false storeFixtureMem (18446744073709551614 : BitVec 64) 2 (9833440827789222417 : BitVec 64)) 42 = 170 := by decide

theorem store4_zero :
    (wmwMem false storeFixtureMem (0 : BitVec 64) 4 (9833440827789222417 : BitVec 64)) 0 = 17 ∧
    (wmwMem false storeFixtureMem (0 : BitVec 64) 4 (9833440827789222417 : BitVec 64)) 1 = 34 ∧
    (wmwMem false storeFixtureMem (0 : BitVec 64) 4 (9833440827789222417 : BitVec 64)) 2 = 51 ∧
    (wmwMem false storeFixtureMem (0 : BitVec 64) 4 (9833440827789222417 : BitVec 64)) 3 = 68 ∧
    (wmwMem false storeFixtureMem (0 : BitVec 64) 4 (9833440827789222417 : BitVec 64)) 18446744073709551615 = 127 ∧
    (wmwMem false storeFixtureMem (0 : BitVec 64) 4 (9833440827789222417 : BitVec 64)) 4 = 132 ∧
    (wmwMem false storeFixtureMem (0 : BitVec 64) 4 (9833440827789222417 : BitVec 64)) 42 = 170 := by decide

theorem store4_wrap :
    (wmwMem false storeFixtureMem (18446744073709551612 : BitVec 64) 4 (9833440827789222417 : BitVec 64)) 18446744073709551612 = 17 ∧
    (wmwMem false storeFixtureMem (18446744073709551612 : BitVec 64) 4 (9833440827789222417 : BitVec 64)) 18446744073709551613 = 34 ∧
    (wmwMem false storeFixtureMem (18446744073709551612 : BitVec 64) 4 (9833440827789222417 : BitVec 64)) 18446744073709551614 = 51 ∧
    (wmwMem false storeFixtureMem (18446744073709551612 : BitVec 64) 4 (9833440827789222417 : BitVec 64)) 18446744073709551615 = 68 ∧
    (wmwMem false storeFixtureMem (18446744073709551612 : BitVec 64) 4 (9833440827789222417 : BitVec 64)) 18446744073709551611 = 123 ∧
    (wmwMem false storeFixtureMem (18446744073709551612 : BitVec 64) 4 (9833440827789222417 : BitVec 64)) 0 = 128 ∧
    (wmwMem false storeFixtureMem (18446744073709551612 : BitVec 64) 4 (9833440827789222417 : BitVec 64)) 42 = 170 := by decide

theorem store8_zero :
    (wmwMem false storeFixtureMem (0 : BitVec 64) 8 (9833440827789222417 : BitVec 64)) 0 = 17 ∧
    (wmwMem false storeFixtureMem (0 : BitVec 64) 8 (9833440827789222417 : BitVec 64)) 1 = 34 ∧
    (wmwMem false storeFixtureMem (0 : BitVec 64) 8 (9833440827789222417 : BitVec 64)) 2 = 51 ∧
    (wmwMem false storeFixtureMem (0 : BitVec 64) 8 (9833440827789222417 : BitVec 64)) 3 = 68 ∧
    (wmwMem false storeFixtureMem (0 : BitVec 64) 8 (9833440827789222417 : BitVec 64)) 4 = 85 ∧
    (wmwMem false storeFixtureMem (0 : BitVec 64) 8 (9833440827789222417 : BitVec 64)) 5 = 102 ∧
    (wmwMem false storeFixtureMem (0 : BitVec 64) 8 (9833440827789222417 : BitVec 64)) 6 = 119 ∧
    (wmwMem false storeFixtureMem (0 : BitVec 64) 8 (9833440827789222417 : BitVec 64)) 7 = 136 ∧
    (wmwMem false storeFixtureMem (0 : BitVec 64) 8 (9833440827789222417 : BitVec 64)) 18446744073709551615 = 127 ∧
    (wmwMem false storeFixtureMem (0 : BitVec 64) 8 (9833440827789222417 : BitVec 64)) 8 = 136 ∧
    (wmwMem false storeFixtureMem (0 : BitVec 64) 8 (9833440827789222417 : BitVec 64)) 42 = 170 := by decide

theorem store8_wrap :
    (wmwMem false storeFixtureMem (18446744073709551608 : BitVec 64) 8 (9833440827789222417 : BitVec 64)) 18446744073709551608 = 17 ∧
    (wmwMem false storeFixtureMem (18446744073709551608 : BitVec 64) 8 (9833440827789222417 : BitVec 64)) 18446744073709551609 = 34 ∧
    (wmwMem false storeFixtureMem (18446744073709551608 : BitVec 64) 8 (9833440827789222417 : BitVec 64)) 18446744073709551610 = 51 ∧
    (wmwMem false storeFixtureMem (18446744073709551608 : BitVec 64) 8 (9833440827789222417 : BitVec 64)) 18446744073709551611 = 68 ∧
    (wmwMem false storeFixtureMem (18446744073709551608 : BitVec 64) 8 (9833440827789222417 : BitVec 64)) 18446744073709551612 = 85 ∧
    (wmwMem false storeFixtureMem (18446744073709551608 : BitVec 64) 8 (9833440827789222417 : BitVec 64)) 18446744073709551613 = 102 ∧
    (wmwMem false storeFixtureMem (18446744073709551608 : BitVec 64) 8 (9833440827789222417 : BitVec 64)) 18446744073709551614 = 119 ∧
    (wmwMem false storeFixtureMem (18446744073709551608 : BitVec 64) 8 (9833440827789222417 : BitVec 64)) 18446744073709551615 = 136 ∧
    (wmwMem false storeFixtureMem (18446744073709551608 : BitVec 64) 8 (9833440827789222417 : BitVec 64)) 18446744073709551607 = 119 ∧
    (wmwMem false storeFixtureMem (18446744073709551608 : BitVec 64) 8 (9833440827789222417 : BitVec 64)) 0 = 128 ∧
    (wmwMem false storeFixtureMem (18446744073709551608 : BitVec 64) 8 (9833440827789222417 : BitVec 64)) 42 = 170 := by decide

private def failedStoreFixture : AsmState 64 :=
  {regs := fun _ => 0, fpRegs := fun _ => 0, mem := fun _ => 99,
   memDomain := fun _ => False, pc := 0, lr := 0, align := 0, be := false, failed := false}

theorem source_failure_writes :
    (writeMemWord (valueWidth := 64) 0 2 1 failedStoreFixture).failed = true ∧
    (writeMemWord (valueWidth := 64) 0 2 1 failedStoreFixture).mem 0 = 1 ∧
    (writeMemWord (valueWidth := 64) 0 2 1 failedStoreFixture).mem 1 = 0 ∧
    (writeMemWord (valueWidth := 64) 0 2 1 failedStoreFixture).mem 2 = 99 := by
  simp [writeMemWord, updMem, assertState, failedStoreFixture]

theorem source_narrow_value :
    (writeMemWord (valueWidth := 1) 0 2 1 failedStoreFixture).failed = true ∧
    (writeMemWord (valueWidth := 1) 0 2 1 failedStoreFixture).mem 0 = 1 ∧
    (writeMemWord (valueWidth := 1) 0 2 1 failedStoreFixture).mem 1 = 0 ∧
    (writeMemWord (valueWidth := 1) 0 2 1 failedStoreFixture).mem 2 = 99 := by
  simp [writeMemWord, updMem, assertState, failedStoreFixture]

end Flapjack.RiscV.TargetProof
