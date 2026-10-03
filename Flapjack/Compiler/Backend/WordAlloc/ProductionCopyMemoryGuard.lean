import Flapjack.RiscV.WordCopyProp
import Flapjack.RiscV.AllocatorMemoryInvariant

namespace Flapjack.WordAlloc
open RiscV

/-- Actual copy rewriting retains memory opcode and offset for arbitrary state.
This is an unconditional extra runtime-domain equality, not HOL correctness. -/
theorem copyInstructionMemoryGuard {α : Type} (state : WordCopyState)
    (instruction : WordInst α) :
    allocatorMemorySupported (.inst (wordCopyInst state instruction).1) =
      allocatorMemorySupported (.inst instruction) := by
  cases instruction with
  | arith operation =>
      cases operation <;> simp [wordCopyInst, allocatorMemorySupported]
  | const register value => simp [wordCopyInst, allocatorMemorySupported]
  | mem operator register address =>
      cases operator <;> simp [wordCopyInst, allocatorMemorySupported]
  | memOffset operator register address offset =>
      cases operator <;> simp [wordCopyInst, allocatorMemorySupported]

/-- Complete executed copy propagation retains the guard, including unchanged
call continuations, with arbitrary input state. No support or target-run
premise is assumed. Flapjack production infrastructure with no HOL original. -/
theorem copyProgramMemoryGuard {α : Type} [WordCseHash α]
    (state : WordCopyState) (program : WordProg α) :
    allocatorMemorySupported (wordCopyProg state program).1 =
      allocatorMemorySupported program := by
  induction state, program using wordCopyProg.induct <;>
    simp_all [wordCopyProg, allocatorMemorySupported]
  all_goals try (split <;> simp_all [allocatorMemorySupported])
  rename_i initial original rewritten final h
  have preserved := copyInstructionMemoryGuard initial original
  simpa only [h] using preserved

/-- Actual wrapper guard equality, without assumed output support. This has
no HOL original and adds no premise to the allocator correctness statement. -/
theorem copyWrapperMemoryGuard {α : Type} [WordCseHash α] (program : WordProg α) :
    allocatorMemorySupported (wordCopyProp program) = allocatorMemorySupported program :=
  copyProgramMemoryGuard wordCopyEmpty program

end Flapjack.WordAlloc
