import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.AllocStore
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GcCall

/-! Relating the allocator's pushed frame to the zero-argument GC call. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend

/-- Flapjack infrastructure: once the collector has returned a replacement
stack, popping the saved frame yields the same state whether or not the
zero-argument call installed temporary locals first. -/
theorem popEnv_callEnv_pushEnv {width : Nat} [NeZero width] {C F : Type}
    (state : WordSemStateFiniteExact width C F) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (ret : WordLocW width) (stack : List (WordSemStackFrame width))
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width)) (memory : BitVec width → WordLocW width) :
    WordSemStateFiniteExact.popEnv
      { WordSemStateFiniteExact.callEnv [ret] (some 0) (WordSemStateFiniteExact.pushEnv envs none state) with
        stack := stack, store := store, memory := memory } =
    WordSemStateFiniteExact.popEnv
      { WordSemStateFiniteExact.pushEnv envs none state with stack := stack, store := store, memory := memory } := by
  have maxEq := callEnv_pushEnv_stackMax state envs ret
  cases stack with
  | nil => rfl
  | cons frame rest =>
    cases frame with
    | stackFrame size nonGc gc handler =>
      cases handler with
      | none =>
        simp only [WordSemStateFiniteExact.popEnv]
        simp only [WordSemStateFiniteExact.callEnv] at maxEq ⊢
        cases pushed : WordSemStateFiniteExact.pushEnv envs none state
        simp_all
      | some info =>
        rcases info with ⟨n, l1, l2⟩
        simp only [WordSemStateFiniteExact.popEnv]
        simp only [WordSemStateFiniteExact.callEnv] at maxEq ⊢
        cases pushed : WordSemStateFiniteExact.pushEnv envs none state
        simp_all

/-- Flapjack infrastructure: after restoring locals, replace the temporary
source stack maximum and safety flag with the actual `addSpace` result, when
the word stack maximum still fits the original source maximum. -/
theorem stateRel64_restoreSource {C F : Type} (conf : Config) (l1 l2 amount : Nat)
    (source : DataSem.State C F) (saved : Spt DataSem.Value)
    (target : WordSemStateFiniteExact 64 C F) (locs : List (Nat × Nat))
    (temporaryMax : Option Nat) (temporarySafe : Bool)
    (related : stateRel64 conf l1 l2
      { source with locals := saved, space := amount, stackMax := temporaryMax, safeForSpace := temporarySafe }
      target none locs)
    (bound : BackendProps.optionLe target.stackMax source.stackMax) :
    stateRel64 conf l1 l2 (DataSem.addSpace { source with locals := saved } amount) target none locs := by
  simp only [stateRel64, DataSem.addSpace] at related ⊢
  tauto

/-- Flapjack infrastructure: execute the production allocator after a valid
source cut. Its successful branch reserves the requested source space; its
failed branch carries the source heap-size lower bound. -/
theorem stateRel64_alloc {C F : Type} (conf : Config) (l1 l2 requested : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (live : NumSet) (saved : Spt DataSem.Value) (cut : DataSem.cutEnv live source.locals = some saved) :
    ∃ (sourceNext : DataSem.State C F) (targetNext : WordSemStateFiniteExact 64 C F) (enough : Bool),
      WordSemStateFiniteExact.alloc (gcAllocSize requested) (adjustSets live) target =
        (if enough then (none, targetNext) else (some .notEnoughSpace, WordSemStateFiniteExact.flushState true targetNext)) ∧
      stateRel64 conf l1 l2 sourceNext targetNext none locs ∧
      sourceNext.locals = saved ∧ sourceNext.stack = source.stack ∧ sourceNext.space = 0 ∧
      targetNext.stackMax = target.stackMax ∧
      sourceNext = { source with locals := saved, space := 0, stackMax :=
        (DataSem.callEnv [] (some 0) (DataSem.pushEnv saved false source)).stackMax, safeForSpace :=
        (DataSem.callEnv [] (some 0) (DataSem.pushEnv saved false source)).safeForSpace } ∧
      targetNext.store.lookup (.temp 29) = target.store.lookup (.temp 29) ∧
      targetNext.store.lookup .allocSize = some (.word (gcAllocSize requested)) ∧
      (enough = true → stateRel64 conf l1 l2 { sourceNext with space := requested } targetNext none locs) ∧
      (enough = true → stateRel64 conf l1 l2 (DataSem.addSpace { source with locals := saved } requested) targetNext none locs) ∧
      (enough = false → conf.gcKind ≠ .none → DataSem.noThunksInRefs source.refs →
        ∀ roots2 dups,
          roots2.Perm (dups ++ (sptToList saved ++ source.stack.flatMap DataSem.extractStack ++ [theGlobal source.global])) →
          (∀ v, v ∈ dups → v ∈ sptToList saved ++ source.stack.flatMap DataSem.extractStack ++ [theGlobal source.global]) →
          source.limits.heapLimit < (DataSem.sizeOfValues source.limits roots2 source.refs .ln).1 + requested) := by
  let target1 := WordSemStateFiniteExact.setStore .allocSize (.word (gcAllocSize requested)) target
  let envs := (sptInter target.locals (.ls ()), sptInter target.locals (adjustSet live))
  let pushed := WordSemStateFiniteExact.pushEnv envs none target1
  let called := WordSemStateFiniteExact.callEnv [.loc l1 l2] (some 0) pushed
  have related1 : stateRel64 conf l1 l2 source target1 none locs :=
    stateRel64_setAllocSize conf l1 l2 source target locs related _
  have cutWord := stateRel64_cutEnvs conf l1 l2 source target locs related live saved cut
  obtain ⟨moved, memory, store, stack, sourceNext, targetNext, run, decoded, _, targetPop,
    restored, storeAfter, temp, alloc, targetMax, sourceLocals, sourceStack, sourceSpace, sourceShape, sizeBound⟩ :=
    stateRel64_gc_savedCall conf l1 l2 requested source target1 locs related1 live saved cut
  have pushedRun : pushed.gcFun (wordSemEncStack pushed.stack, pushed.memory, pushed.mdomain, pushed.store) =
      some (moved, memory, store) := by
    change pushed.gcFun (wordSemEncStack pushed.stack, pushed.memory, pushed.mdomain, pushed.store) =
      some (moved, memory, store) at run
    exact run
  have pushedDecoded : wordSemDecStack moved pushed.stack = some stack := by
    change wordSemDecStack moved pushed.stack = some stack at decoded
    exact decoded
  have actualGc : WordSemStateFiniteExact.gc pushed =
      some { pushed with stack := stack, store := store, memory := memory } := by
    simp [WordSemStateFiniteExact.gc, pushedRun, pushedDecoded]
  have actualPop : WordSemStateFiniteExact.popEnv { pushed with stack := stack, store := store, memory := memory } =
      some targetNext := by
    rw [← popEnv_callEnv_pushEnv target1 envs (.loc l1 l2) stack store memory]
    change WordSemStateFiniteExact.popEnv { called with stack := stack, store := store, memory := memory } =
      some targetNext at targetPop
    exact targetPop
  have target1Alloc : target1.store.lookup .allocSize = some (.word (gcAllocSize requested)) := by
    simp [target1, WordSemStateFiniteExact.setStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
  have targetAlloc : targetNext.store.lookup .allocSize = some (.word (gcAllocSize requested)) := by
    rw [alloc]
    exact target1Alloc
  have tempPreserved : targetNext.store.lookup (.temp 29) = target.store.lookup (.temp 29) := by
    simpa [target1, WordSemStateFiniteExact.setStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using temp
  obtain ⟨nextFree, trigger, _, nextStore, triggerStore, _, _, _, _⟩ :=
    stateRel64_spaceAvailable conf l1 l2 sourceNext targetNext locs restored
  let enough := decide ((gcAllocSize requested : BitVec 64).toNat ≤ (trigger - nextFree).toNat)
  have check : WordSemStateFiniteExact.hasSpace (.word (gcAllocSize requested)) targetNext = some enough := by
    simp [WordSemStateFiniteExact.hasSpace, WordSemStateFiniteExact.getStore, nextStore, triggerStore, enough]
  refine ⟨sourceNext, targetNext, enough, ?_, restored, sourceLocals, sourceStack, sourceSpace,
    ?_, sourceShape, tempPreserved, targetAlloc, ?_, ?_, ?_⟩
  · simp [WordSemStateFiniteExact.alloc, cutWord, actualGc, actualPop,
      WordSemStateFiniteExact.getStore, targetAlloc, check, pushed, envs, target1]
    cases enough <;> rfl
  · simpa [target1, WordSemStateFiniteExact.setStore] using targetMax
  · intro yes
    apply stateRel64_hasSpace conf l1 l2 requested sourceNext targetNext locs restored
    simpa [yes] using check
  · intro yes
    have reserved := stateRel64_hasSpace conf l1 l2 requested sourceNext targetNext locs restored (by simpa [yes] using check)
    have maxBound : BackendProps.optionLe targetNext.stackMax source.stackMax := by
      rw [show targetNext.stackMax = target.stackMax by simpa [target1, WordSemStateFiniteExact.setStore] using targetMax]
      exact related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    rw [sourceShape] at reserved
    apply stateRel64_restoreSource conf l1 l2 requested source saved targetNext locs
      (DataSem.callEnv [] (some 0) (DataSem.pushEnv saved false source)).stackMax
      (DataSem.callEnv [] (some 0) (DataSem.pushEnv saved false source)).safeForSpace ?_ maxBound
    simpa using reserved
  · intro no active noThunks
    apply sizeBound ⟨target1Alloc, ?_, active, noThunks⟩
    simpa [no] using check

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
