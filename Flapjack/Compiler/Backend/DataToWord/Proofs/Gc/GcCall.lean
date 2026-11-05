import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateGcSize
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.PushCall
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.PopEnv

/-! Collector calls with the live source environment saved on the stack. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend

/-- Flapjack infrastructure: a state relation with no extra roots also holds
with an explicitly empty extra-root list. -/
theorem stateRel64_none_to_empty {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs) :
    stateRel64 conf l1 l2 source target (some []) locs := by
  simp only [stateRel64, Option.getD_none, Option.getD_some, List.nil_append] at related ⊢
  tauto

/-- Flapjack infrastructure: restoring a word frame preserves its store. -/
theorem wordPopEnv_store {width : Nat} [NeZero width] {C F : Type}
    (before after : WordSemStateFiniteExact width C F)
    (pop : WordSemStateFiniteExact.popEnv before = some after) : after.store = before.store := by
  cases h : before.stack with
  | nil => simp [WordSemStateFiniteExact.popEnv, h] at pop
  | cons frame rest =>
    cases frame with
    | stackFrame size nonGc gc handler =>
      cases handler with
      | none => simp [WordSemStateFiniteExact.popEnv, h] at pop; subst after; rfl
      | some info =>
        rcases info with ⟨saved, l1, l2⟩
        simp [WordSemStateFiniteExact.popEnv, h] at pop
        subst after
        rfl

/-- Flapjack infrastructure: popping a word frame preserves the recorded
stack maximum. -/
theorem wordPopEnv_stackMax {width : Nat} [NeZero width] {C F : Type}
    (before after : WordSemStateFiniteExact width C F)
    (pop : WordSemStateFiniteExact.popEnv before = some after) : after.stackMax = before.stackMax := by
  cases h : before.stack with
  | nil => simp [WordSemStateFiniteExact.popEnv, h] at pop
  | cons frame rest =>
    cases frame with
    | stackFrame size nonGc gc handler =>
      cases handler with
      | none => simp [WordSemStateFiniteExact.popEnv, h] at pop; subst after; rfl
      | some info =>
        rcases info with ⟨saved, l1, l2⟩
        simp [WordSemStateFiniteExact.popEnv, h] at pop
        subst after
        rfl

/-- Flapjack infrastructure: saving a frame does not increase the recorded
stack maximum when the current stack and locals already fit that maximum. -/
theorem pushEnv_stackMax_of_bound {width : Nat} [NeZero width] {C F : Type}
    (state : WordSemStateFiniteExact width C F) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (bound : BackendProps.optionLe (wordSemOptionAdd (wordSemStackSize state.stack) state.localsSize) state.stackMax) :
    (WordSemStateFiniteExact.pushEnv envs none state).stackMax = state.stackMax := by
  have reverseBound : BackendProps.optionLe
      (wordSemOptionAdd state.localsSize (wordSemStackSize state.stack)) state.stackMax := by
    cases hsize : wordSemStackSize state.stack <;> cases hlocals : state.localsSize <;>
      cases hmax : state.stackMax <;> simp_all [BackendProps.optionLe, wordSemOptionAdd, Nat.add_comm]
  have maxEq : wordSemOptionMax state.stackMax
      (wordSemOptionAdd state.localsSize (wordSemStackSize state.stack)) = state.stackMax := by
    cases hsize : wordSemStackSize state.stack <;> cases hlocals : state.localsSize <;>
      cases hmax : state.stackMax <;>
      simp_all [BackendProps.optionLe, wordSemOptionAdd, wordSemOptionMax]
  cases envList : wordSemEnvToList envs.2 state.permute with
  | mk gc permute =>
    change wordSemOptionMax state.stackMax
      (wordSemStackSize (.stackFrame state.localsSize (sptToAList envs.1) gc none :: state.stack)) = state.stackMax
    change wordSemOptionMax state.stackMax
      (wordSemOptionAdd state.localsSize (wordSemStackSize state.stack)) = state.stackMax
    exact maxEq


/-- Flapjack infrastructure: recording the same stack size twice, with zero
extra call-frame size, does not change the optional stack maximum. -/
theorem optionMax_add_zero_repeat (maxSize stackSize : Option Nat) :
    wordSemOptionMax (wordSemOptionMax maxSize stackSize)
      (wordSemOptionAdd stackSize (some 0)) = wordSemOptionMax maxSize stackSize := by
  cases maxSize <;> cases stackSize <;> simp [wordSemOptionMax, wordSemOptionAdd]

/-- Flapjack infrastructure: entering the zero-argument collector call does
not change the stack maximum already recorded by saving the environment. -/
theorem callEnv_pushEnv_stackMax {width : Nat} [NeZero width] {C F : Type}
    (state : WordSemStateFiniteExact width C F) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (ret : WordLocW width) :
    (WordSemStateFiniteExact.callEnv [ret] (some 0) (WordSemStateFiniteExact.pushEnv envs none state)).stackMax =
      (WordSemStateFiniteExact.pushEnv envs none state).stackMax := by
  cases envList : wordSemEnvToList envs.2 state.permute with
  | mk gc permute =>
    simpa [WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv, envList] using
      optionMax_add_zero_repeat state.stackMax
        (wordSemStackSize (.stackFrame state.localsSize (sptToAList envs.1) gc none :: state.stack))

/-- Flapjack infrastructure: save the live source environment, enter a
zero-argument collector call, execute collection, and restore the saved
frames. The sizing conclusion is expressed over the saved environment and
source stack through the intermediate state's extracted roots. -/
theorem stateRel64_gc_savedCall {C F : Type} (conf : Config) (l1 l2 requested : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (live : NumSet) (saved : Spt DataSem.Value) (cut : DataSem.cutEnv live source.locals = some saved) :
    let source0 := DataSem.callEnv [] (some 0) (DataSem.pushEnv saved false source)
    let target0 := WordSemStateFiniteExact.callEnv [.loc l1 l2] (some 0)
      (WordSemStateFiniteExact.pushEnv (sptInter target.locals (.ls ()), sptInter target.locals (adjustSet live))
        none target)
    ∃ moved memory store stack sourceNext targetNext,
      target0.gcFun (wordSemEncStack target0.stack, target0.memory, target0.mdomain, target0.store) =
        some (moved, memory, store) ∧
      wordSemDecStack moved target0.stack = some stack ∧
      DataSem.popEnv { source0 with space := 0 } = some sourceNext ∧
      WordSemStateFiniteExact.popEnv { target0 with stack := stack, store := store, memory := memory } = some targetNext ∧
      stateRel64 conf l1 l2 sourceNext targetNext none locs ∧
      targetNext.store = store ∧
      targetNext.store.lookup (.temp 29) = target.store.lookup (.temp 29) ∧
      targetNext.store.lookup .allocSize = target.store.lookup .allocSize ∧
      targetNext.stackMax = target.stackMax ∧
      sourceNext.locals = saved ∧ sourceNext.stack = source.stack ∧ sourceNext.space = 0 ∧
      sourceNext = { source with locals := saved, space := 0, stackMax := source0.stackMax, safeForSpace := source0.safeForSpace } ∧
      (target.store.lookup .allocSize = some (.word (gcAllocSize requested)) ∧
        WordSemStateFiniteExact.hasSpace (.word (gcAllocSize requested)) targetNext = some false ∧
        conf.gcKind ≠ .none ∧ DataSem.noThunksInRefs source.refs →
        ∀ roots2 dups,
          roots2.Perm (dups ++ (sptToList saved ++ source.stack.flatMap DataSem.extractStack ++ [theGlobal source.global])) →
          (∀ v, v ∈ dups → v ∈ sptToList saved ++ source.stack.flatMap DataSem.extractStack ++ [theGlobal source.global]) →
          source.limits.heapLimit < (DataSem.sizeOfValues source.limits roots2 source.refs .ln).1 + requested) := by
  let source0 := DataSem.callEnv [] (some 0) (DataSem.pushEnv saved false source)
  let target0 := WordSemStateFiniteExact.callEnv [.loc l1 l2] (some 0)
    (WordSemStateFiniteExact.pushEnv (sptInter target.locals (.ls ()), sptInter target.locals (adjustSet live))
      none target)
  have entered : stateRel64 conf l1 l2 source0 target0 none ((l1, l2) :: locs) := by
    have increased := stateRel64_withClock conf l1 l2 source target none locs (source.clock + 1) related
    have entry := stateRel64_pushCall conf l1 l2 l1 l2 { source with clock := source.clock + 1 }
      { target with clock := source.clock + 1 } locs increased [] [] [] (some 0)
      (by rfl) (by rfl) live saved (by simpa using cut) none
    have sameClock := related.2.1
    have sourceClock : DataSem.decClock { source with clock := source.clock + 1 } = source := by
      cases source
      simp [DataSem.decClock]
    have targetClock : WordSemStateFiniteExact.decClock { target with clock := source.clock + 1 } = target := by
      cases target
      simp [WordSemStateFiniteExact.decClock]
      exact sameClock.symm
    rw [sourceClock, targetClock] at entry
    exact entry
  have empty : source0.locals = .ln := by simp [source0, DataSem.callEnv, sptFromList]
  obtain ⟨moved, memory, store, stack, run, decoded, temp, alloc, preserved, sizeBound⟩ :=
    stateRel64_gc_gen conf l1 l2 requested source0 target0 ((l1, l2) :: locs) entered empty
  let sourceNext := { { source0 with space := 0 } with
    locals := saved, stack := source.stack, localsSize := source.localsSize }
  have sourcePop : DataSem.popEnv { source0 with space := 0 } = some sourceNext := by
    simp [source0, sourceNext, DataSem.callEnv, DataSem.pushEnv, DataSem.popEnv]
  have withEmpty := stateRel64_none_to_empty conf l1 l2 { source0 with space := 0 }
    { target0 with stack := stack, store := store, memory := memory } ((l1, l2) :: locs) preserved
  obtain ⟨targetNext, return1, return2, remaining, targetPop, locations, restored, _⟩ :=
    stateRel64_popEnv conf l1 l2 { source0 with space := 0 } sourceNext
      { target0 with stack := stack, store := store, memory := memory } [] ((l1, l2) :: locs) withEmpty sourcePop
  have same : l1 = return1 ∧ l2 = return2 ∧ locs = remaining := by simpa [and_assoc] using locations
  rcases same with ⟨rfl, rfl, rfl⟩
  have storeAfter : targetNext.store = store := wordPopEnv_store _ _ targetPop
  have sameSpace : WordSemStateFiniteExact.hasSpace (.word (gcAllocSize requested)) targetNext =
      WordSemStateFiniteExact.hasSpace (.word (gcAllocSize requested)) { target0 with store := store } := by
    simp [WordSemStateFiniteExact.hasSpace, WordSemStateFiniteExact.getStore, storeAfter]
  have targetStore : target0.store = target.store := by
    simp [target0, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv]
  have targetMax : target0.stackMax = target.stackMax := by
    have savedMax := pushEnv_stackMax_of_bound target
      (sptInter target.locals (.ls ()), sptInter target.locals (adjustSet live))
      related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have callMax := callEnv_pushEnv_stackMax target
      (sptInter target.locals (.ls ()), sptInter target.locals (adjustSet live)) (.loc l1 l2)
    exact callMax.trans savedMax
  have maxAfter : targetNext.stackMax = target.stackMax := by
    exact (wordPopEnv_stackMax _ _ targetPop).trans targetMax
  refine ⟨moved, memory, store, stack, sourceNext, targetNext, run, decoded, sourcePop, targetPop,
    restored, storeAfter, ?_, ?_, maxAfter, rfl, rfl, rfl, ?_, ?_⟩
  · simpa [storeAfter, targetStore] using temp
  · simpa [storeAfter, targetStore] using alloc
  · cases source
    simp [sourceNext, source0, DataSem.callEnv, DataSem.pushEnv]
  · rintro ⟨allocated, failed, active, noThunks⟩
    have allocated0 : target0.store.lookup .allocSize = some (.word (gcAllocSize requested)) := by
      simpa [targetStore] using allocated
    have failed0 : WordSemStateFiniteExact.hasSpace (.word (gcAllocSize requested))
        { target0 with store := store } = some false := by
      rw [← sameSpace]
      exact failed
    have result := sizeBound ⟨allocated0, failed0, active, noThunks⟩
    simpa [source0, DataSem.callEnv, DataSem.pushEnv, DataSem.extractStack] using result

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
