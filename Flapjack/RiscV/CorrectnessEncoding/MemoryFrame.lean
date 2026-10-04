import Flapjack.RiscV.CorrectnessEncoding.MemoryInputs
import Flapjack.RiscV.CorrectnessEncoding.MemorySource

/-! Outside-source-domain frames needed by the original Mem assertions.
These are untagged local compositions with no separately named HOL originals.
Literal source mem_store success derives its footprint and LOG2 alignment;
the native raw store frame preserves every other byte. No target run result,
alignment guard or desired post-state is assumed. -/
namespace Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
  Compiler.Encoders.RiscV.Target
set_option autoImplicit false

/-- Successful literal source stores derive every native alignment and region
obligation internally. Native state and stored value are arbitrary. -/
theorem source_success_native_store_frame (r : Nat) (address : HolAddr 64)
    (s : AsmState 64) (t : riscv_state) (v : BitVec 64) (k : Fin 4)
    (little : s.be = false)
    (success : (memStore ((2 : Nat) ^ k.val) r address s).failed = false)
    (x : BitVec 64) (outside : ¬ s.memDomain x) :
    (rawWriteData (addrHOL address s, v, (2 : Nat) ^ k.val) t).MEM8 x = t.MEM8 x := by
  have guards := (source_memstore_success ((2 : Nat) ^ k.val) r address s).mp success
  have log : holLOG2 ((2 : Nat) ^ k.val) = k.val := by
    have sizes : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ k.val = 3 := by
      have := k.isLt
      omega
    rcases sizes with h | h | h | h <;> simp [h, holLOG2_eq_log2]
  have aligned : holAligned k.val (addrHOL address s) = true := by
    simpa only [log] using guards.2.2
  have domain : ∀ j, j < (2 : Nat) ^ k.val →
      s.memDomain (addrHOL address s + BitVec.ofNat 64 j) := by
    have footprint := guards.2.1
    simp only [little, Bool.false_eq_true, reduceIte] at footprint
    exact (source_memory_domain_little _ _ _).mp footprint
  apply memory_raw_write_aligned_frame _ _ _ k aligned x
  intro j bound equal
  apply outside
  rw [equal]
  exact domain j bound

/-- Every actual emitted memory Run preserves bytes outside the original source
domain. Original asmStep and initial relation supply success, register/address
correspondence and all native guards; no target-run premise is introduced. -/
theorem memory_run_outside_source_domain (m : HolMemop) (r base : Nat)
    (w : BitVec 64) (s s' : AsmState 64) (t : riscv_state) (native : instruction)
    (step : asmStep riscvConfig s (.inst (.mem m r (.addr base w))) s')
    (relation : targetStateRel riscvTarget s t)
    (emitted : native ∈ riscvAst (.inst (.mem m r (.addr base w))))
    (x : BitVec 64) (outside : ¬ s.memDomain x) :
    (Run native t).MEM8 x = t.MEM8 x := by
  have ok := step.2.2.2.2.2.2
  have little : s.be = false := step.2.2.1
  have success := step.2.2.2.2.2.1
  have update := step.2.2.2.2.1
  rw [← update] at success
  have success : (memOp m r (.addr base w) s).failed = false := by
    simpa only [asmUpd, instUpd, updPc, Bool.not_eq_true] using success
  cases m
  all_goals rw [memory_emitted_run _ r base w s t native ok relation emitted]
  all_goals simp only [memOp] at success
  · simp only [«write'GPR»]
    split <;> rfl
  · simp only [«write'GPR»]
    split <;> rfl
  · simp only [«write'GPR»]
    split <;> rfl
  · simp only [«write'GPR»]
    split <;> rfl
  · simpa only [Nat.reducePow, Nat.reduceDiv] using
      source_success_native_store_frame r (.addr base w) s t (readReg r s)
        ⟨3, by decide⟩ little success x outside
  · simpa only [Nat.reducePow, Nat.reduceDiv] using
      source_success_native_store_frame r (.addr base w) s t (readReg r s)
        ⟨0, by decide⟩ little success x outside
  · simpa only [Nat.reducePow, Nat.reduceDiv] using
      source_success_native_store_frame r (.addr base w) s t (readReg r s)
        ⟨1, by decide⟩ little success x outside
  · simpa only [Nat.reducePow, Nat.reduceDiv] using
      source_success_native_store_frame r (.addr base w) s t (readReg r s)
        ⟨2, by decide⟩ little success x outside

end Flapjack.RiscV.TargetProof
