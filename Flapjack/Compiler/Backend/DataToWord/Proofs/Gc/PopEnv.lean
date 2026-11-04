import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.JumpExcLocals

/-! Restoring a caller frame after returning from a data-to-word call. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend.BackendProps

/-- Restoring either kind of frame uses at most its prior stack footprint. -/
theorem wordStackSize_restore_frame_le {width : Nat} [NeZero width]
    (size : Option Nat) (nonGc gc : List (Nat × WordLocW width))
    (handler : Option (Nat × Nat × Nat)) (rest : List (WordSemStackFrame width)) :
    optionLe (wordSemOptionAdd (wordSemStackSize rest) size)
      (wordSemStackSize (.stackFrame size nonGc gc handler :: rest)) := by
  cases handler with
  | none =>
    change optionLe (wordSemOptionAdd (wordSemStackSize rest) size)
      (wordSemOptionAdd size (wordSemStackSize rest))
    generalize wordSemStackSize rest = total
    cases size <;> cases total <;> simp [wordSemOptionAdd, optionLe]
    omega
  | some info =>
    obtain ⟨saved, a, b⟩ := info
    exact wordStackSize_restore_handler_le size nonGc gc saved a b rest

/-- Generic reconstruction of related caller states from corresponding top
frames. Extra returned roots remain represented while the saved locals are
restored. The explicit frame equations allow either ordinary or handler frames. -/
theorem stateRel64_restoreFrame {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (roots : List (DataSem.Value × WordLocW 64)) (locs : List (Nat × Nat))
    (related : stateRel64 conf l1 l2 source target (some roots) locs)
    (rest : List DataSem.Stack) (size size' : Option Nat)
    (env : Spt DataSem.Value) (nonGc gc : List (Nat × WordLocW 64))
    (handler : Option (Nat × Nat × Nat)) (wordRest : List (WordSemStackFrame 64))
    (targetStack : target.stack = .stackFrame size' nonGc gc handler :: wordRest)
    (headRel : stackEnvRel size size' env nonGc gc)
    (headRoots : flatStack source.stack target.stack = joinEnv env gc ++ flatStack rest wordRest)
    (savedSource savedTarget : Nat) (sameHandler : savedTarget = savedSource)
    (return1 return2 : Nat) (remaining : List (Nat × Nat))
    (savedLoc : containsLoc (.stackFrame size' nonGc gc handler) (return1, return2))
    (locationTail : List.Forall₂ containsLoc wordRest remaining)
    (stackTail : List.Forall₂ stackRel rest wordRest) :
    let sourceNext := { source with locals := env, stack := rest, localsSize := size, handler := savedSource }
    let targetNext := { target with locals := sptUnion (sptFromAList gc) (sptFromAList nonGc), stack := wordRest, localsSize := size', handler := savedTarget }
    stateRel64 conf return1 return2 sourceNext targetNext none remaining ∧
      Memory.memoryRel conf targetNext.be (holThe sourceNext.tstamps) sourceNext.refs sourceNext.space
        targetNext.store targetNext.memory targetNext.mdomain
        (roots ++ joinEnv sourceNext.locals (sptToAList (sptInter targetNext.locals (adjustSet sourceNext.locals))) ++
          [(theGlobal sourceNext.global, holFapply targetNext.store .globals)] ++ flatStack sourceNext.stack targetNext.stack) := by
  rcases related with ⟨ffi, clock, _, gcFun, code, oracle, dimension, shift, timestamps, globals,
    _, _, _, _, stackBound, maxBound, stackSize, _, limits, memory⟩
  have restoredBound : optionLe (wordSemOptionAdd (wordSemStackSize wordRest) size') target.stackMax := by
    have tail := wordStackSize_restore_frame_le size' nonGc gc handler wordRest
    have stackOnly := optionLe_wordSemOptionAdd_left (wordSemStackSize target.stack) target.localsSize
    rw [targetStack] at stackOnly stackBound
    exact optionLe_trans _ _ _ ⟨tail, optionLe_trans _ _ _ ⟨stackOnly, stackBound⟩⟩
  have carried : Memory.memoryRel conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain
      (roots ++ joinEnv env (sptToAList (sptInter (sptUnion (sptFromAList gc) (sptFromAList nonGc)) (adjustSet env))) ++
        [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack rest wordRest) := by
    apply Memory.memoryRel_rearrange conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain _ _ ?_ memory
    intro pair member
    simp only [Option.getD_some, List.mem_append, List.mem_singleton] at member ⊢
    rw [headRoots]
    simp only [List.mem_append]
    rcases member with ((root | localRoot) | global) | stack
    · exact Or.inl (Or.inl (Or.inl root))
    · exact Or.inr (Or.inl (stackEnvRel_restored_roots size size' env nonGc gc headRel localRoot))
    · exact Or.inl (Or.inr global)
    · exact Or.inr (Or.inr stack)
  have retained : Memory.memoryRel conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain
      (joinEnv env (sptToAList (sptInter (sptUnion (sptFromAList gc) (sptFromAList nonGc)) (adjustSet env))) ++
        [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack rest wordRest) := by
    apply Memory.memoryRel_rearrange conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain _ _ ?_ carried
    intro pair member
    simp only [List.mem_append] at member ⊢
    rcases member with (localRoot | global) | stack
    · exact Or.inl (Or.inl (Or.inr localRoot))
    · exact Or.inl (Or.inr global)
    · exact Or.inr stack
  refine ⟨?_, carried⟩
  refine ⟨ffi, clock, sameHandler, gcFun, code, oracle, dimension, shift, timestamps, globals, ?_, ?_,
    stackTail, locationTail, restoredBound, maxBound, stackSize, headRel.2.1.symm, limits, ?_⟩
  · intro _
    exact stackEnvRel_restored_zero size size' env nonGc gc headRel return1 return2 savedLoc
  · intro n present
    exact stackEnvRel_restored_present size size' env nonGc gc headRel n present
  · simpa using retained

/-- A successful source pop has a matching word pop. Saved return roots
remain represented while the candidate relation is restored. -/
theorem stateRel64_popEnv {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source next : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (roots : List (DataSem.Value × WordLocW 64)) (locs : List (Nat × Nat))
    (related : stateRel64 conf l1 l2 source target (some roots) locs)
    (pop : DataSem.popEnv source = some next) :
    ∃ targetNext return1 return2 remaining,
      WordSemStateFiniteExact.popEnv target = some targetNext ∧
      locs = (return1, return2) :: remaining ∧
      stateRel64 conf return1 return2 next targetNext none remaining ∧
      Memory.memoryRel conf targetNext.be (holThe next.tstamps) next.refs next.space
        targetNext.store targetNext.memory targetNext.mdomain
        (roots ++ joinEnv next.locals (sptToAList (sptInter targetNext.locals (adjustSet next.locals))) ++
          [(theGlobal next.global, holFapply targetNext.store .globals)] ++ flatStack next.stack targetNext.stack) := by
  have stackPairs := related.2.2.2.2.2.2.2.2.2.2.2.2.1
  have locPairs := related.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  cases sourceStack : source.stack with
  | nil => simp [DataSem.popEnv, sourceStack] at pop
  | cons dataFrame rest =>
    rw [sourceStack] at stackPairs
    cases targetStack : target.stack with
    | nil => rw [targetStack] at stackPairs; cases stackPairs
    | cons wordFrame wordRest =>
      rw [targetStack] at stackPairs locPairs
      cases stackPairs with
      | cons headRel stackTail =>
        cases locs with
        | nil => cases locPairs
        | cons returnLoc remaining =>
          cases locPairs with
          | cons savedLoc locationTail =>
            obtain ⟨r1, r2⟩ := returnLoc
            cases wordFrame with
            | stackFrame size' nonGc gc handler =>
              cases dataFrame with
              | env size env =>
                cases handler with
                | none =>
                  simp only [stackRel] at headRel
                  simp [DataSem.popEnv, sourceStack] at pop
                  subst next
                  have headRoots : flatStack source.stack target.stack = joinEnv env gc ++ flatStack rest wordRest := by
                    simp [sourceStack, targetStack, flatStack]
                  have restored := stateRel64_restoreFrame conf l1 l2 source target roots ((r1, r2) :: remaining) related
                    rest size size' env nonGc gc none wordRest targetStack headRel headRoots
                    source.handler target.handler related.2.2.1 r1 r2 remaining savedLoc locationTail stackTail
                  refine ⟨_, r1, r2, remaining, ?_, rfl, restored⟩
                  simp [WordSemStateFiniteExact.popEnv, targetStack]
                | some info => simp [stackRel] at headRel
              | exc size env saved =>
                cases handler with
                | none => simp [stackRel] at headRel
                | some info =>
                  obtain ⟨saved', a, b⟩ := info
                  simp only [stackRel] at headRel
                  simp [DataSem.popEnv, sourceStack] at pop
                  subst next
                  have headRoots : flatStack source.stack target.stack = joinEnv env gc ++ flatStack rest wordRest := by
                    simp [sourceStack, targetStack, flatStack]
                  have restored := stateRel64_restoreFrame conf l1 l2 source target roots ((r1, r2) :: remaining) related
                    rest size size' env nonGc gc (some (saved', a, b)) wordRest targetStack headRel.1 headRoots
                    saved saved' headRel.2 r1 r2 remaining savedLoc locationTail stackTail
                  refine ⟨_, r1, r2, remaining, ?_, rfl, restored⟩
                  simp [WordSemStateFiniteExact.popEnv, targetStack]

/-- A single returned pair can be installed after popping either frame kind. -/
theorem stateRel64_popEnv_setVar {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source next : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (value : DataSem.Value) (word : WordLocW 64) (locs : List (Nat × Nat))
    (related : stateRel64 conf l1 l2 source target (some [(value, word)]) locs)
    (pop : DataSem.popEnv source = some next) (dest : Nat) :
    ∃ targetNext return1 return2 remaining,
      WordSemStateFiniteExact.popEnv target = some targetNext ∧
      locs = (return1, return2) :: remaining ∧
      stateRel64 conf return1 return2 (DataSem.setVar dest value next)
        (WordSemStateFiniteExact.setVar (adjustVar dest) word targetNext) none remaining := by
  obtain ⟨targetNext, r1, r2, remaining, targetPop, locations, after, carried⟩ :=
    stateRel64_popEnv conf l1 l2 source next target [(value, word)] locs related pop
  refine ⟨targetNext, r1, r2, remaining, targetPop, locations, ?_⟩
  apply stateRel64_setNewLocal conf r1 r2 next targetNext remaining after dest value word
  simpa using carried

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
