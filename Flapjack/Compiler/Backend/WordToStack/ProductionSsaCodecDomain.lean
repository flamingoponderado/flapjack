import Flapjack.RiscV.Allocator
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.Domain

namespace Flapjack
open WordProgCarrierCodec

/-- Flapjack-only scaffolding for the actual SSA codec domain; no HOL original. -/
@[simp] private theorem supportsCodec_wordSsaSeq {α : Type u}
    (first second : WordProg α) :
    supportsCodec (wordSsaSeq first second) =
      (supportsCodec first && supportsCodec second) := by
  unfold wordSsaSeq
  split <;> simp_all [supportsCodec]

/-- Flapjack-only scaffolding for the actual SSA codec domain; no HOL original. -/
private theorem supportsCodec_wordSsaRenameInst {α : Type u}
    (state : WordSsaState) (instruction : WordInst α) :
    supportsCodec (.inst (wordSsaRenameInst state instruction).2) =
      supportsCodec (.inst instruction) := by
  cases instruction with
  | arith operation => cases operation <;> simp [wordSsaRenameInst, wordSsaFresh, supportsCodec]
  | const destination value => simp [wordSsaRenameInst, wordSsaFresh, supportsCodec]
  | mem operation destination address => cases operation <;> simp [wordSsaRenameInst, wordSsaFresh, supportsCodec]
  | memOffset operation destination address offset => cases operation <;> simp [wordSsaRenameInst, wordSsaFresh, supportsCodec]

/-- Flapjack-only scaffolding for the actual SSA codec domain; no HOL original. -/
private theorem supportsCodec_wordSsaRenameInstProgram {α : Type u} [OfNat α 0]
    (state : WordSsaState) (instruction : WordInst α) :
    supportsCodec (wordSsaRenameInstProgram state instruction).2 =
      supportsCodec (.inst instruction) := by
  unfold wordSsaRenameInstProgram
  split <;> simp [supportsCodec, wordSsaFresh,
    supportsCodec_wordSsaRenameInst]

/-- Flapjack-only scaffolding for the actual SSA codec domain; no HOL original. -/
@[simp] private theorem supportsCodec_wordSsaRenameMove {α : Type u}
    (state : WordSsaState) (priority : Nat) (moves : List (Nat × Nat)) :
    supportsCodec (wordSsaRenameMove (α := α) state priority moves).2 = true := by
  simp [wordSsaRenameMove, supportsCodec]

/-- Flapjack-only scaffolding for the actual SSA codec domain; no HOL original. -/
@[simp] private theorem supportsCodec_wordSsaListNextVarRenameMove {α : Type u}
    (state : WordSsaState) (next : Nat) (names : List Nat) :
    supportsCodec (wordSsaListNextVarRenameMove (α := α) state next names).2.2 = true := by
  simp [wordSsaListNextVarRenameMove, supportsCodec]

/-- Flapjack-only scaffolding for the actual SSA codec domain; no HOL original. -/
@[simp] private theorem supportsCodec_wordSsaReconcileTo {α : Type u}
    (source target : WordSsaState) (names : List Nat) :
    supportsCodec (wordSsaReconcileTo (α := α) source target names) = true := by
  unfold wordSsaReconcileTo
  dsimp only
  split <;> simp [supportsCodec]

/-- Flapjack-only scaffolding for the actual SSA codec domain; no HOL original. -/
@[simp] private theorem supportsCodec_wordSsaFakeMoves {α : Type u} [OfNat α 0]
    (names : List Nat) :
    supportsCodec (wordSsaFakeMoves (α := α) names) = true := by
  induction names <;> simp_all [wordSsaFakeMoves, supportsCodec]

/-- Flapjack-only scaffolding for the actual SSA codec domain; no HOL original. -/
@[simp] private theorem supportsCodec_wordSsaLoopSetup {α : Type u} [OfNat α 0]
    (state : WordSsaState) (liveIn liveOut : List Nat) :
    supportsCodec (wordSsaLoopSetup (α := α) state liveIn liveOut).2 = true := by
  simp [wordSsaLoopSetup, supportsCodec]

/-- Flapjack-only scaffolding for the actual SSA codec domain; no HOL original. -/
private theorem supportsCodec_wordSsaFakeInconsistencyMoves
    {α : Type u} [OfNat α 0] (preferred : Option Bool) (names : List Nat)
    (left right : WordSsaState) (next : Nat) :
    supportsCodec (wordSsaFakeInconsistencyMoves (α := α)
      preferred names left right next).1 = true ∧
    supportsCodec (wordSsaFakeInconsistencyMoves (α := α)
      preferred names left right next).2.1 = true := by
  induction names generalizing left right next with
  | nil => simp [wordSsaFakeInconsistencyMoves, supportsCodec]
  | cons name names ih =>
    simp only [wordSsaFakeInconsistencyMoves]
    try dsimp only
    split <;> simp_all [supportsCodec]

/-- Flapjack-only scaffolding for the actual SSA codec domain; no HOL original. -/
@[simp] private theorem supportsCodec_wordSsaFixInconsistencies
    {α : Type u} [OfNat α 0] (preferred : Option Bool)
    (left right : WordSsaState) (next : Nat) :
    supportsCodec (wordSsaFixInconsistencies (α := α)
      preferred left right next).2.1 = true ∧
    supportsCodec (wordSsaFixInconsistencies (α := α)
      preferred left right next).2.2 = true := by
  unfold wordSsaFixInconsistencies
  dsimp only
  simp only [supportsCodec, wordSsaPriorityMove, Bool.true_and]
  exact supportsCodec_wordSsaFakeInconsistencyMoves preferred _ _ _ _

/-- Flapjack-only scaffolding for the actual SSA codec domain; no HOL original. -/
private theorem supportsCodec_wordSsaRenameProgramWithLoops
    {α : Type u} [OfNat α 0] (frames : List WordSsaLoopFrame)
    (state : WordSsaState) (program : WordProg α) :
    supportsCodec (wordSsaRenameProgramWithLoops frames state program).2 =
      supportsCodec program := by
  induction frames, state, program using wordSsaRenameProgramWithLoops.induct
  case case41 =>
    rename_i frames inputState op condition right thenBranch elseBranch leftState leftProgram leftEq elseInput rightState rightProgram rightEq preferred merged leftMoves rightMoves fixEq ih2 ih1
    have repair := supportsCodec_wordSsaFixInconsistencies (α := α) preferred leftState rightState rightState.next
    rw [fixEq] at repair
    rw [wordSsaRenameProgramWithLoops]
    simp_all (config := { zetaDelta := true }) [supportsCodec]
  all_goals rw [wordSsaRenameProgramWithLoops]
  all_goals try subst_vars
  all_goals simp_all (config := { zetaDelta := true }) [supportsCodec, wordSsaFresh,
      supportsCodec_wordSsaRenameInstProgram,
      supportsCodec_wordSsaSeq,
      supportsCodec_wordSsaListNextVarRenameMove,
      supportsCodec_wordSsaReconcileTo,
      supportsCodec_wordSsaFixInconsistencies]

  all_goals grind only [supportsCodec_wordSsaListNextVarRenameMove,
    supportsCodec_wordSsaLoopSetup,
    supportsCodec_wordSsaFixInconsistencies]

/-- Flapjack-only scaffolding for the actual SSA codec domain; no HOL original. -/
private theorem supportsCodec_wordFullSsaCcTrans
    {α : Type u} [OfNat α 0] (parameterCount : Nat) (program : WordProg α) :
    supportsCodec (wordFullSsaCcTrans parameterCount program).2.2 =
      supportsCodec program := by
  simp [wordFullSsaCcTrans, wordSsaRenameFunctionWithEntry,
    wordSsaRenameFunction, wordSsaRenameProgram, wordSsaEntryMove,
    supportsCodec, supportsCodec_wordSsaRenameProgramWithLoops]

/-- Complete codec-domain preservation through the actual executed recursive
SSA transform, for arbitrary program, state and loop frames. The private
structural predicate is eliminated using its full equality with the actual
encoder. No codec-success, supported-input, desired-output or successful-pass
premise is assumed. Flapjack-only carrier infrastructure, not a HOL port. -/
theorem wordLangProgToHOL_wordSsaRenameProgramWithLoops_isSome {width : Nat}
    (frames : List WordSsaLoopFrame) (state : WordSsaState)
    (program : WordProg (BitVec width)) :
    (wordLangProgToHOL (wordSsaRenameProgramWithLoops frames state program).2).isSome =
      (wordLangProgToHOL program).isSome := by
  rw [codecDomain, codecDomain]
  exact supportsCodec_wordSsaRenameProgramWithLoops frames state program

/-- The actual ABI-entry SSA wrapper preserves exactly the initial native
codec domain, including rejected nested five-register arithmetic. No caller
assumption about the output codec is used. Flapjack-only carrier closure;
post-SSA optimisation closure and the native frame/route remain separate. -/
theorem wordLangProgToHOL_wordFullSsaCcTrans_isSome {width : Nat}
    (parameterCount : Nat) (program : WordProg (BitVec width)) :
    (wordLangProgToHOL (wordFullSsaCcTrans parameterCount program).2.2).isSome =
      (wordLangProgToHOL program).isSome := by
  rw [codecDomain, codecDomain]
  exact supportsCodec_wordFullSsaCcTrans parameterCount program

end Flapjack
