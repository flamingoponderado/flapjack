import Flapjack.Compiler.Encoders.AsmProps.Memory
import Flapjack.Compiler.Encoders.AsmSem.MemOps
import Flapjack.RiscV.CorrectnessEncoding.MemoryStep

/-! Source traversal assertions needed by original native Mem correctness.
No separately named HOL theorem is claimed: these are local consequences of
literal asmSem read_mem_word/write_mem_word, preserving arbitrary counts,
both endian branches, independent result/value widths and modular addresses.
The final encoder must obtain success from its original asm_step premise. -/
namespace Flapjack.RiscV.TargetProof
open Flapjack Compiler.Encoders.Asm Compiler.Encoders.AsmSem
set_option autoImplicit false

/-- The literal recursive footprint of the source memory operations. This
predicate records domain assertions, not successful native execution. -/
def sourceMemoryDomain {width : Nat} (be : Bool) (d : BitVec width → Prop)
    (a : BitVec width) : Nat → Prop
  | 0 => True
  | n + 1 => d a ∧ sourceMemoryDomain be d (if be then a - 1 else a + 1) n

/-- Exact source read success iff the incoming state has not failed and every
literal traversal address is in its domain. No count/endian/width restriction.
Untagged infrastructure; no separately named HOL original. -/
theorem source_read_success {width resultWidth : Nat} [NeZero width] [NeZero resultWidth]
    (a : BitVec width) (n : Nat) (s : AsmState width) :
    (readMemWord (resultWidth := resultWidth) a n s).2.failed = false ↔
      s.failed = false ∧ sourceMemoryDomain s.be s.memDomain a n := by
  induction n generalizing a with
  | zero => simp [readMemWord, sourceMemoryDomain]
  | succ n ih =>
    rw [readMemWord_succ]
    have dom := (sndReadMemWordConsts (resultWidth := resultWidth) n
      (if s.be then a - 1 else a + 1) s).2.2.2
    dsimp only
    simp only [assertState, Bool.or_eq_false_iff, Bool.not_eq_false', dom,
      decide_eq_true_eq, ih, sourceMemoryDomain]
    tauto

/-- Exact source write success characterizes the same traversal assertions,
including completed writes on failure. Values retain their independent width.
Untagged infrastructure; no separately named HOL original. -/
theorem source_write_success {width valueWidth : Nat} [NeZero width] [NeZero valueWidth]
    (a : BitVec width) (n : Nat) (v : BitVec valueWidth) (s : AsmState width) :
    (writeMemWord a n v s).failed = false ↔
      s.failed = false ∧ sourceMemoryDomain s.be s.memDomain a n := by
  induction n generalizing a v with
  | zero => simp [writeMemWord, sourceMemoryDomain]
  | succ n ih =>
    rw [writeMemWord_succ]
    have dom := writeMemWord_mem_domain (valueWidth := valueWidth) n
      (if s.be then a - 1 else a + 1) (v >>> (8 : Nat)) s
    simp only [assertState, updMem, Bool.or_eq_false_iff, Bool.not_eq_false', dom,
      decide_eq_true_eq, ih, sourceMemoryDomain]
    tauto

/-- Literal little-endian traversal is the wrapping byte region used by the
native memory proof. Arbitrary counts and addresses, including wraparound.
No separately named HOL theorem is claimed. -/
theorem source_memory_domain_little {width : Nat} (d : BitVec width → Prop)
    (a : BitVec width) (n : Nat) :
    sourceMemoryDomain false d a n ↔ ∀ j, j < n → d (a + BitVec.ofNat width j) := by
  induction n generalizing a with
  | zero => simp [sourceMemoryDomain]
  | succ n ih =>
    simp only [sourceMemoryDomain, Bool.false_eq_true, reduceIte, ih]
    constructor
    · rintro ⟨head, tail⟩ j hj
      cases j with
      | zero => simpa using head
      | succ j =>
        have h := tail j (by omega)
        have address : (a + 1) + BitVec.ofNat width j = a + BitVec.ofNat width (j + 1) := by
          rw [show j + 1 = 1 + j by omega, BitVec.ofNat_add]
          exact BitVec.add_assoc _ _ _
        simpa only [address, Nat.succ_eq_add_one] using h
    · intro h
      constructor
      · simpa using h 0 (by omega)
      · intro j hj
        have h' := h (j + 1) (by omega)
        have address : (a + 1) + BitVec.ofNat width j = a + BitVec.ofNat width (j + 1) := by
          rw [show j + 1 = 1 + j by omega, BitVec.ofNat_add]
          exact BitVec.add_assoc _ _ _
        rw [← address] at h'
        exact h'

/-- Literal big-endian traversal is the wrapping byte region used by the
native memory proof. Arbitrary counts and addresses, including wraparound.
No separately named HOL theorem is claimed. -/
theorem source_memory_domain_big {width : Nat} (d : BitVec width → Prop)
    (a : BitVec width) (n : Nat) :
    sourceMemoryDomain true d a n ↔ ∀ j, j < n → d (a - BitVec.ofNat width j) := by
  induction n generalizing a with
  | zero => simp [sourceMemoryDomain]
  | succ n ih =>
    simp only [sourceMemoryDomain, reduceIte, ih]
    constructor
    · rintro ⟨head, tail⟩ j hj
      cases j with
      | zero => simpa using head
      | succ j =>
        have h := tail j (by omega)
        have address : (a - 1) - BitVec.ofNat width j = a - BitVec.ofNat width (j + 1) := by
          rw [show j + 1 = 1 + j by omega, BitVec.ofNat_add]
          exact BitVec.sub_sub _ _ _
        simpa only [address, Nat.succ_eq_add_one] using h
    · intro h
      constructor
      · simpa using h 0 (by omega)
      · intro j hj
        have h' := h (j + 1) (by omega)
        have address : (a - 1) - BitVec.ofNat width j = a - BitVec.ofNat width (j + 1) := by
          rw [show j + 1 = 1 + j by omega, BitVec.ofNat_add]
          exact BitVec.sub_sub _ _ _
        rw [← address] at h'
        exact h'

/-- Derive the actual native byte region from successful source reads in the
original little-endian target. Success is the source evaluator result, not a
native run premise. No separately named HOL theorem is claimed. -/
theorem source_read_domain {width resultWidth : Nat} [NeZero width] [NeZero resultWidth]
    (a : BitVec width) (n : Nat) (s : AsmState width) (little : s.be = false)
    (success : (readMemWord (resultWidth := resultWidth) a n s).2.failed = false) :
    ∀ j, j < n → s.memDomain (a + BitVec.ofNat width j) := by
  have footprint := ((source_read_success a n s).mp success).2
  rw [little, source_memory_domain_little] at footprint
  exact footprint

/-- The same original source-domain derivation for writes, with no value/count
or native-run assumption. No separately named HOL theorem is claimed. -/
theorem source_write_domain {width valueWidth : Nat} [NeZero width] [NeZero valueWidth]
    (a : BitVec width) (n : Nat) (v : BitVec valueWidth) (s : AsmState width)
    (little : s.be = false) (success : (writeMemWord a n v s).failed = false) :
    ∀ j, j < n → s.memDomain (a + BitVec.ofNat width j) := by
  have footprint := ((source_write_success a n v s).mp success).2
  rw [little, source_memory_domain_little] at footprint
  exact footprint

/-- Full literal source mem_load success extracts its original alignment and
recursive domain assertions. This is local infrastructure, not a tagged port
or an extra native execution premise. No byte-count or endian restriction. -/
theorem source_memload_success {width : Nat} [NeZero width]
    (n r : Nat) (address : HolAddr width) (s : AsmState width) :
    (memLoad n r address s).failed = false ↔
      s.failed = false ∧
      sourceMemoryDomain s.be s.memDomain
        (if s.be then addrHOL address s + BitVec.ofNat width (n - 1) else addrHOL address s) n ∧
      holAligned (holLOG2 n) (addrHOL address s) = true := by
  simp only [memLoad]
  simp only [assertState, updReg, Bool.or_eq_false_iff, Bool.not_eq_false']
  rw [source_read_success]
  tauto

/-- Full literal source mem_store success extracts the same original guards,
with all incoming failures and completed writes preserved. Untagged local
infrastructure; no separately named HOL theorem is claimed. -/
theorem source_memstore_success {width : Nat} [NeZero width]
    (n r : Nat) (address : HolAddr width) (s : AsmState width) :
    (memStore n r address s).failed = false ↔
      s.failed = false ∧
      sourceMemoryDomain s.be s.memDomain
        (if s.be then addrHOL address s + BitVec.ofNat width (n - 1) else addrHOL address s) n ∧
      holAligned (holLOG2 n) (addrHOL address s) = true := by
  simp only [memStore]
  simp only [assertState, Bool.or_eq_false_iff, Bool.not_eq_false']
  rw [source_write_success]
  tauto

end Flapjack.RiscV.TargetProof
