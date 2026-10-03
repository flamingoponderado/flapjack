import Flapjack.Compiler.Encoders.RiscV.Target.State
import Flapjack.Misc.BytesInMemory
import Flapjack.Compiler.Encoders.AsmProps.PcCoverage

/-! Full literal native target-state byte lemmas. The first original theorem
has an unused polymorphic `w : α`; it is retained explicitly. The second uses
a word64 offset. Both retain all original conclusions and premises. -/
namespace Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 Compiler.Encoders.RiscV.Target

@[hol "cakeml/compiler/encoders/riscv/proofs/riscv_targetProofScript.sml" "bytes_in_memory_thm"]
theorem bytes_in_memory_thm {α : Type} (_w : α) (s : AsmState 64) (state : riscv_state)
    (a b c d : BitVec 8)
    (h : targetStateRel riscvTarget s state ∧
      bytesInMemoryHOL (s.pc) [a,b,c,d] s.mem s.memDomain) :
    state.exception = exception.NoException ∧
    (state.c_MCSR state.procID).mstatus.VM = 0 ∧
    (state.c_MCSR state.procID).mcpuid.ArchBase = 2 ∧
    state.c_NextFetch state.procID = none ∧
    holAligned 2 (state.c_PC state.procID) = true ∧
    state.MEM8 (state.c_PC state.procID) = a ∧
    state.MEM8 (state.c_PC state.procID + 1) = b ∧
    state.MEM8 (state.c_PC state.procID + 2) = c ∧
    state.MEM8 (state.c_PC state.procID + 3) = d ∧
    s.memDomain (state.c_PC state.procID + 3) ∧
    s.memDomain (state.c_PC state.procID + 2) ∧
    s.memDomain (state.c_PC state.procID + 1) ∧
    s.memDomain (state.c_PC state.procID) := by
  have hp := h.1.2.1
  change state.c_PC state.procID = s.pc at hp
  have hm := h.1.2.2.1
  change ∀ x, s.memDomain x → state.MEM8 x = s.mem x at hm
  have hb := h.2
  have two : (1 : BitVec 64) + 1 = 2 := by decide
  have three : (2 : BitVec 64) + 1 = 3 := by decide
  simp only [bytesInMemoryHOL] at hb
  rcases hb with ⟨ha, da, hb, db, hc, dc, hd, dd, _⟩
  have hok := (riscvOk_iff state).mp h.1.1
  rcases hok with ⟨vm, arch, fetch, ex, aligned⟩
  refine ⟨ex, vm, arch, fetch, aligned, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hp]; exact (hm _ da).trans ha
  · rw [hp]; exact (hm _ db).trans hb
  · rw [hp]; simpa only [BitVec.add_assoc, two] using (hm _ dc).trans hc
  · rw [hp]; simpa only [BitVec.add_assoc, two, three] using (hm _ dd).trans hd
  · rw [hp]; simpa only [BitVec.add_assoc, two, three] using dd
  · rw [hp]; simpa only [BitVec.add_assoc, two] using dc
  · rw [hp]; exact db
  · rw [hp]; exact da

@[hol "cakeml/compiler/encoders/riscv/proofs/riscv_targetProofScript.sml" "bytes_in_memory_thm2"]
theorem bytes_in_memory_thm2 (w : BitVec 64) (s : AsmState 64) (state : riscv_state)
    (a b c d : BitVec 8)
    (h : targetStateRel riscvTarget s state ∧
      bytesInMemoryHOL (s.pc + w) [a,b,c,d] s.mem s.memDomain) :
    state.MEM8 (state.c_PC state.procID + w) = a ∧
    state.MEM8 (state.c_PC state.procID + w + 1) = b ∧
    state.MEM8 (state.c_PC state.procID + w + 2) = c ∧
    state.MEM8 (state.c_PC state.procID + w + 3) = d ∧
    s.memDomain (state.c_PC state.procID + w + 3) ∧
    s.memDomain (state.c_PC state.procID + w + 2) ∧
    s.memDomain (state.c_PC state.procID + w + 1) ∧
    s.memDomain (state.c_PC state.procID + w) := by
  have hp := h.1.2.1
  change state.c_PC state.procID = s.pc at hp
  have hm := h.1.2.2.1
  change ∀ x, s.memDomain x → state.MEM8 x = s.mem x at hm
  have hb := h.2
  have two : (1 : BitVec 64) + 1 = 2 := by decide
  have three : (2 : BitVec 64) + 1 = 3 := by decide
  simp only [bytesInMemoryHOL] at hb
  rcases hb with ⟨ha, da, hb, db, hc, dc, hd, dd, _⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hp]; exact (hm _ da).trans ha
  · rw [hp]; exact (hm _ db).trans hb
  · rw [hp]; simpa only [BitVec.add_assoc, two] using (hm _ dc).trans hc
  · rw [hp]; simpa only [BitVec.add_assoc, two, three] using (hm _ dd).trans hd
  · rw [hp]; simpa only [BitVec.add_assoc, two, three] using dd
  · rw [hp]; simpa only [BitVec.add_assoc, two] using dc
  · rw [hp]; exact db
  · rw [hp]; exact da

/-- Full original domain-to-all-instruction-byte environment agreement. -/
@[hol "cakeml/compiler/encoders/riscv/proofs/riscv_targetProofScript.sml"
  "bytes_in_memory_IMP_all_pcs_MEM8"]
theorem bytes_in_memory_IMP_all_pcs_MEM8
    (env : Nat → riscv_state → riscv_state) (a : BitVec 64)
    (xs : List (BitVec 8)) (m : BitVec 64 → BitVec 8) (dm : BitVec 64 → Prop)
    (h : bytesInMemoryHOL a xs m dm ∧
      ∀ (i : Nat) (ms' : riscv_state), ∀ address, dm address →
        (env i ms').MEM8 address = ms'.MEM8 address) :
    ∀ (i : Nat) (ms' : riscv_state), ∀ pc,
      pc ∈ Compiler.Encoders.AsmProps.allPcs xs.length a 0 →
        (env i ms').MEM8 pc = ms'.MEM8 pc := by
  intro i ms' pc hpc
  exact h.2 i ms' pc
    (Compiler.Encoders.AsmProps.bytesInMemory_allPcs xs a m dm 0 h.1 hpc)

end Flapjack.RiscV.TargetProof
