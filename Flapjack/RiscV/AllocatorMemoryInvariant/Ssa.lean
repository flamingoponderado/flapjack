import Flapjack.RiscV.AllocatorMemoryInvariant
import Flapjack.RiscV.Allocator

namespace Flapjack.RiscV

/-- Flapjack-specific: SSA's smart sequence preserves the conjunction of the
ordinary-memory support predicates. There is no separate HOL theorem for this
production-carrier invariant. -/
@[simp] theorem allocatorMemorySupported_wordSsaSeq {α : Type u}
    (first second : WordProg α) :
    allocatorMemorySupported (wordSsaSeq first second) =
      (allocatorMemorySupported first && allocatorMemorySupported second) := by
  cases first <;> cases second <;> simp [wordSsaSeq, allocatorMemorySupported]

/-- Flapjack-specific: the instruction renamer changes register names, never
ordinary-memory opcodes. The invariant concerns the actual executed helper. -/
theorem allocatorMemorySupported_wordSsaRenameInst {α : Type u}
    (state : WordSsaState) (instruction : WordInst α) :
    allocatorMemorySupported (.inst (wordSsaRenameInst state instruction).2) =
      allocatorMemorySupported (.inst instruction) := by
  cases instruction with
  | arith operation => cases operation <;> simp [wordSsaRenameInst, wordSsaFresh, allocatorMemorySupported]
  | const destination value => simp [wordSsaRenameInst, wordSsaFresh, allocatorMemorySupported]
  | mem operation destination address => cases operation <;> simp [wordSsaRenameInst, wordSsaFresh, allocatorMemorySupported]
  | memOffset operation destination address offset => cases operation <;> simp [wordSsaRenameInst, wordSsaFresh, allocatorMemorySupported]

/-- Flapjack-only: fixed-register arithmetic scaffolding contains no ordinary
memory opcode, and the remaining instruction route preserves its opcode. -/
theorem allocatorMemorySupported_wordSsaRenameInstProgram {α : Type u} [OfNat α 0]
    (state : WordSsaState) (instruction : WordInst α) :
    allocatorMemorySupported (wordSsaRenameInstProgram state instruction).2 =
      allocatorMemorySupported (.inst instruction) := by
  unfold wordSsaRenameInstProgram
  split <;> simp [allocatorMemorySupported, wordSsaFresh,
    allocatorMemorySupported_wordSsaRenameInst]

/-- Flapjack-only: renaming a move only emits a move. -/
@[simp] theorem allocatorMemorySupported_wordSsaRenameMove {α : Type u}
    (state : WordSsaState) (priority : Nat) (moves : List (Nat × Nat)) :
    allocatorMemorySupported (wordSsaRenameMove (α := α) state priority moves).2 = true := by
  simp [wordSsaRenameMove, allocatorMemorySupported]

/-- Flapjack-only: stack-save/restore renaming only emits a move. -/
@[simp] theorem allocatorMemorySupported_wordSsaListNextVarRenameMove {α : Type u}
    (state : WordSsaState) (next : Nat) (names : List Nat) :
    allocatorMemorySupported (wordSsaListNextVarRenameMove (α := α) state next names).2.2 = true := by
  simp [wordSsaListNextVarRenameMove, allocatorMemorySupported]

/-- Flapjack-only: loop-edge reconciliation emits only Skip or Move. -/
@[simp] theorem allocatorMemorySupported_wordSsaReconcileTo {α : Type u}
    (source target : WordSsaState) (names : List Nat) :
    allocatorMemorySupported (wordSsaReconcileTo (α := α) source target names) = true := by
  unfold wordSsaReconcileTo
  dsimp only
  split <;> simp [allocatorMemorySupported]

/-- Flapjack-only: initialization of one-sided SSA names uses constants only. -/
@[simp] theorem allocatorMemorySupported_wordSsaFakeMoves {α : Type u} [OfNat α 0]
    (names : List Nat) :
    allocatorMemorySupported (wordSsaFakeMoves (α := α) names) = true := by
  induction names <;> simp_all [wordSsaFakeMoves, allocatorMemorySupported]

/-- Flapjack-only: loop setup uses only constant initialization and moves. -/
@[simp] theorem allocatorMemorySupported_wordSsaLoopSetup {α : Type u} [OfNat α 0]
    (state : WordSsaState) (liveIn liveOut : List Nat) :
    allocatorMemorySupported (wordSsaLoopSetup (α := α) state liveIn liveOut).2 = true := by
  simp [wordSsaLoopSetup, allocatorMemorySupported]

/-- Flapjack-only: both sides of the one-sided-name repair emit just moves
and constants, for every state and fresh-name seed. -/
theorem allocatorMemorySupported_wordSsaFakeInconsistencyMoves
    {α : Type u} [OfNat α 0] (preferred : Option Bool) (names : List Nat)
    (left right : WordSsaState) (next : Nat) :
    allocatorMemorySupported (wordSsaFakeInconsistencyMoves (α := α)
      preferred names left right next).1 = true ∧
    allocatorMemorySupported (wordSsaFakeInconsistencyMoves (α := α)
      preferred names left right next).2.1 = true := by
  induction names generalizing left right next with
  | nil => simp [wordSsaFakeInconsistencyMoves, allocatorMemorySupported]
  | cons name names ih =>
    simp only [wordSsaFakeInconsistencyMoves]
    try dsimp only
    split <;> simp_all [allocatorMemorySupported]

/-- Flapjack-only: branch and call reconciliation repairs emit no unsupported
ordinary-memory instruction. -/
@[simp] theorem allocatorMemorySupported_wordSsaFixInconsistencies
    {α : Type u} [OfNat α 0] (preferred : Option Bool)
    (left right : WordSsaState) (next : Nat) :
    allocatorMemorySupported (wordSsaFixInconsistencies (α := α)
      preferred left right next).2.1 = true ∧
    allocatorMemorySupported (wordSsaFixInconsistencies (α := α)
      preferred left right next).2.2 = true := by
  unfold wordSsaFixInconsistencies
  dsimp only
  simp only [allocatorMemorySupported, wordSsaPriorityMove, Bool.true_and]
  exact allocatorMemorySupported_wordSsaFakeInconsistencyMoves preferred _ _ _ _

/-- Flapjack-only: the actual recursive SSA/calling-convention transform
preserves the ordinary-memory support Boolean, for arbitrary loop frames and
SSA states. This includes both optional Call bodies and all generated repairs. -/
theorem allocatorMemorySupported_wordSsaRenameProgramWithLoops
    {α : Type u} [OfNat α 0] (frames : List WordSsaLoopFrame)
    (state : WordSsaState) (program : WordProg α) :
    allocatorMemorySupported (wordSsaRenameProgramWithLoops frames state program).2 =
      allocatorMemorySupported program := by
  induction frames, state, program using wordSsaRenameProgramWithLoops.induct
  case case43 =>
    rename_i frames inputState op condition right thenBranch elseBranch leftState leftProgram leftEq elseInput rightState rightProgram rightEq preferred merged leftMoves rightMoves fixEq ih2 ih1
    have repair := allocatorMemorySupported_wordSsaFixInconsistencies (α := α) preferred leftState rightState rightState.next
    rw [fixEq] at repair
    rw [wordSsaRenameProgramWithLoops]
    simp_all (config := { zetaDelta := true }) [allocatorMemorySupported]
  all_goals rw [wordSsaRenameProgramWithLoops]
  all_goals try subst_vars
  all_goals simp_all (config := { zetaDelta := true }) [allocatorMemorySupported, wordSsaFresh,
      allocatorMemorySupported_wordSsaRenameInstProgram,
      allocatorMemorySupported_wordSsaSeq,
      allocatorMemorySupported_wordSsaReconcileTo]

  all_goals grind only [allocatorMemorySupported_wordSsaListNextVarRenameMove,
    allocatorMemorySupported_wordSsaLoopSetup,
    allocatorMemorySupported_wordSsaFixInconsistencies]

/-- Flapjack-specific: the executed parameter-count SSA boundary adds only
supported ABI entry moves and preserves the support Boolean of its input.
This is not a HOL theorem port; it proves closure for the production carrier. -/
theorem allocatorMemorySupported_wordFullSsaCcTrans
    {α : Type u} [OfNat α 0] (parameterCount : Nat) (program : WordProg α) :
    allocatorMemorySupported (wordFullSsaCcTrans parameterCount program).2.2 =
      allocatorMemorySupported program := by
  simp [wordFullSsaCcTrans, wordSsaRenameFunctionWithEntry,
    wordSsaRenameFunction, wordSsaRenameProgram, wordSsaEntryMove,
    allocatorMemorySupported, allocatorMemorySupported_wordSsaRenameProgramWithLoops]

/-- Flapjack-specific ordinary-memory support is preserved without assuming
anything about the transformed result or its allocator execution. -/
theorem wordFullSsaCcTrans_preserves_allocatorMemorySupported
    {α : Type u} [OfNat α 0] (parameterCount : Nat) (program : WordProg α)
    (supported : allocatorMemorySupported program = true) :
    allocatorMemorySupported (wordFullSsaCcTrans parameterCount program).2.2 = true := by
  rw [allocatorMemorySupported_wordFullSsaCcTrans, supported]

end Flapjack.RiscV
