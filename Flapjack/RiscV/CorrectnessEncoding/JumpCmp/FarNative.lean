import Flapjack.RiscV.CorrectnessEncoding.JumpCmp.Prefix

/-! Actual inverse branches for far JumpCmp lowering. Local untagged
compositions retain the original native branch semantics. -/
namespace Flapjack.RiscV.TargetProof.JumpCmp
open Flapjack RiscV.L3 RiscV.L3.Step Compiler.Encoders.Asm
  Compiler.Encoders.RiscV.Target

theorem inverse_simple_branch_next (c : Cmp) (r s : BitVec 5)
    (ms : riscv_state) (ok : riscvOk ms = true)
    (simple : c ≠ .test ∧ c ≠ .notTest)
    (bytes : encodedInstructionBytes ms (simple_branch (inverse_cmp c) r s 4)) :
    NextRISCV ms = some (Jump.branchPost ms
      (if wordCmpHOL c (GPR r ms) (GPR s ms) then
        ms.c_PC ms.procID + 4 else ms.c_PC ms.procID + 8)) := by
  have next := simple_branch_next (inverse_cmp c) r s 4 ms ok
    (inverse_simple c simple) bytes
  rw [inverse_word_cmp] at next
  cases decision : wordCmpHOL c (GPR r ms) (GPR s ms) <;>
    simpa [decision] using next

theorem inverse_test_kind (c : Cmp) :
    (inverse_cmp c = .test ∨ inverse_cmp c = .notTest) ↔
      (c = .test ∨ c = .notTest) := by
  cases c <;> simp [inverse_cmp]

/-- The original prefix value serves the inverse branch too: only the
comparison polarity changes, never the scratch computation. -/
theorem inverse_immediate_branch_next (c : Cmp) (r : BitVec 5)
    (left i : BitVec 64) (ms : riscv_state) (ok : riscvOk ms = true)
    (read : GPR r ms = left)
    (scratch : GPR (31#5) ms =
      if c = .test ∨ c = .notTest then left &&& i else i)
    (bytes : encodedInstructionBytes ms (immediate_branch (inverse_cmp c) r 4)) :
    NextRISCV ms = some (Jump.branchPost ms
      (if wordCmpHOL c left i then ms.c_PC ms.procID + 4 else ms.c_PC ms.procID + 8)) := by
  have value : GPR (31#5) ms =
      if inverse_cmp c = .test ∨ inverse_cmp c = .notTest then left &&& i else i := by
    simpa only [inverse_test_kind] using scratch
  have next := immediate_branch_next (inverse_cmp c) r left i 4 ms ok read value bytes
  rw [inverse_word_cmp] at next
  cases decision : wordCmpHOL c left i <;> simpa [decision] using next

 theorem inverse_test_branch_next (c : Cmp) (left right : BitVec 64)
    (ms : riscv_state) (ok : riscvOk ms = true)
    (test : c = .test ∨ c = .notTest)
    (scratch : GPR (31#5) ms = left &&& right)
    (bytes : encodedInstructionBytes ms (simple_branch (inverse_cmp c) 31 0 4)) :
    NextRISCV ms = some (Jump.branchPost ms
      (if wordCmpHOL c left right then ms.c_PC ms.procID + 4 else ms.c_PC ms.procID + 8)) := by
  have next := test_branch_next (inverse_cmp c) left right 4 ms ok
    ((inverse_test_kind c).mpr test) scratch bytes
  rw [inverse_word_cmp] at next
  cases decision : wordCmpHOL c left right <;> simpa [decision] using next

end Flapjack.RiscV.TargetProof.JumpCmp
