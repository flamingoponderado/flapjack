import Flapjack.RiscV.WordDeadCode

namespace Flapjack.WordAlloc
open RiscV

/-- Instruction deletion retains support whenever its input is supported.
This is the extra Flapjack runtime-domain guard, not a HOL correctness port. -/
private theorem deadInstructionMemoryGuard {α : Type} (live : List Nat)
    (instruction : WordInst α)
    (supported : allocatorMemorySupported (.inst instruction) = true) :
    allocatorMemorySupported (wordDeadInst live instruction).1 = true := by
  unfold wordDeadInst
  split <;> simp_all [allocatorMemorySupported]

private theorem deadMoveMemoryGuard {α : Type} (priority : Nat) (live : List Nat)
    (moves : List (Nat × Nat)) :
    allocatorMemorySupported (wordDeadMove (α := α) priority live moves).1 = true := by
  unfold wordDeadMove
  dsimp only
  split <;> simp [allocatorMemorySupported]

/-- The complete actual fallback deletion pass preserves the input memory
domain for arbitrary backward state. Deletion may remove an unsupported
instruction, so the result is support preservation rather than equality.
This has no HOL original and supplies no target evaluation assumption. -/
theorem deadFallbackMemoryGuard {α : Type} [WordCseHash α]
    (program : WordProg α) (live : List Nat) (frames : List (List Nat × List Nat))
    (returnLabels nlive : List Nat)
    (supported : allocatorMemorySupported program = true) :
    allocatorMemorySupported (wordDeadCodeWithStores program live frames returnLabels nlive).1 = true := by
  fun_induction wordApplyColour (fun name => name) program generalizing live frames returnLabels nlive <;>
    simp_all [wordDeadCodeWithStores, allocatorMemorySupported, wordDeadCodeAuxWithLabels,
      deadInstructionMemoryGuard, deadMoveMemoryGuard]
  case case7 =>
    cases ‹WordExp α› <;> simp_all [allocatorMemorySupported]
    split <;> simp_all [allocatorMemorySupported]
  all_goals repeat' (split <;> simp_all [allocatorMemorySupported])

/-- Actual fallback cleanup retains source support; no output-support premise
is assumed. Flapjack production infrastructure, not HOL pass correctness. -/
theorem removeDeadFallbackMemoryGuard {α : Type} [WordCseHash α]
    (program : WordProg α) (supported : allocatorMemorySupported program = true) :
    allocatorMemorySupported (wordRemoveDeadProgram program) = true := by
  exact deadFallbackMemoryGuard program [] [] (wordDeadReturnLabels program) [] supported

end Flapjack.WordAlloc
