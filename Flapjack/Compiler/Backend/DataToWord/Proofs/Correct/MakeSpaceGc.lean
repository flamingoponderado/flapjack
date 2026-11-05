import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.SilentFfi
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.AllocCall

/-! Connecting the compiled slow allocation path to the production collector. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- Flapjack infrastructure: the compiler's overflow-checked request is the
same word used by the garbage-collector correctness argument. -/
theorem makeSpaceRequest64_eq_gcAllocSize (amount : Nat) :
    makeSpaceRequest64 amount = gcAllocSize amount := by
  simp [makeSpaceRequest64, gcAllocSize, BitVec.toNat_ofNat]


/-- Flapjack infrastructure: the actual compiled slow path reaches the
proved allocator result for both successful and failed space checks. The
word evaluator's enclosing clock adjustment is retained explicitly. -/
theorem makeSpace64_slow_allocator {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (amount : Nat) (live : NumSet) (saved : Spt DataSem.Value)
    (cut : DataSem.cutEnv live source.locals = some saved)
    (nextFree trigger : BitVec 64)
    (nextStore : target.store.lookup .nextFree = some (.word nextFree))
    (triggerStore : target.store.lookup .triggerGC = some (.word trigger))
    (slow : Compiler.Encoders.Asm.wordCmpHOL .lower (trigger - nextFree) (makeSpaceRequest64 amount) = true)
    (noFfi : conf.callEmptyFfi = false) :
    let prepared := WordSemStateFiniteExact.setVar 1 (.word (makeSpaceRequest64 amount))
      (WordSemStateFiniteExact.setVar 1 (.word (trigger - nextFree)) target)
    ∃ (sourceNext : DataSem.State C F) (targetNext : WordSemStateFiniteExact 64 C F) (enough : Bool),
      WordSemStateFiniteExact.evaluate (compileControl64 conf secn label (.makeSpace amount live)).1 target =
        WordSemStateFiniteExact.fixClock prepared
          (if enough then (none, targetNext) else (some .notEnoughSpace, WordSemStateFiniteExact.flushState true targetNext)) ∧
      stateRel64 conf l1 l2 sourceNext targetNext none locs ∧
      sourceNext.locals = saved ∧ sourceNext.stack = source.stack ∧ sourceNext.space = 0 ∧
      (enough = true → stateRel64 conf l1 l2 { sourceNext with space := amount } targetNext none locs) ∧
      (enough = true → stateRel64 conf l1 l2 (DataSem.addSpace { source with locals := saved } amount) targetNext none locs) ∧
      (enough = false → conf.gcKind ≠ .none → DataSem.noThunksInRefs source.refs →
        ∀ roots2 dups,
          roots2.Perm (dups ++ (sptToList saved ++ source.stack.flatMap DataSem.extractStack ++ [theGlobal source.global])) →
          (∀ v, v ∈ dups → v ∈ sptToList saved ++ source.stack.flatMap DataSem.extractStack ++ [theGlobal source.global]) →
          source.limits.heapLimit < (DataSem.sizeOfValues source.limits roots2 source.refs .ln).1 + amount) := by
  let prepared := WordSemStateFiniteExact.setVar 1 (.word (makeSpaceRequest64 amount))
    (WordSemStateFiniteExact.setVar 1 (.word (trigger - nextFree)) target)
  have firstRel := stateRel64_setScratch1 conf l1 l2 source target locs related (.word (trigger - nextFree))
  have preparedRel : stateRel64 conf l1 l2 source prepared none locs :=
    stateRel64_setScratch1 conf l1 l2 source _ locs firstRel (.word (makeSpaceRequest64 amount))
  obtain ⟨sourceNext, targetNext, enough, alloc, nextRel, sourceLocals, sourceStack, sourceSpace,
    _, _, _, _, reserve, originalReserve, failed⟩ := stateRel64_alloc conf l1 l2 amount source prepared locs preparedRel live saved cut
  refine ⟨sourceNext, targetNext, enough, ?_, nextRel, sourceLocals, sourceStack, sourceSpace, reserve, originalReserve, failed⟩
  rw [makeSpace64_slow_noFfi conf secn label target amount live nextFree trigger nextStore triggerStore slow noFfi]
  change WordSemStateFiniteExact.fixClock prepared
    (WordSemStateFiniteExact.evaluate (.alloc 1 (adjustSets live)) prepared) = _
  have read : WordSemStateFiniteExact.getVar 1 prepared = some (.word (makeSpaceRequest64 amount)) := by
    simp [prepared, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
  simp only [WordSemStateFiniteExact.evaluate, read, makeSpaceRequest64_eq_gcAllocSize, alloc]
  simp only [prepared, makeSpaceRequest64_eq_gcAllocSize]

/-- For either diagnostic configuration, the compiled slow path reaches the
allocator with the source live environment and a related word state. The
remaining sequence includes the real allocator and the post-allocation FFI. -/
theorem makeSpace64_slow_enterAllocator {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (amount : Nat) (live : NumSet) (saved : Spt DataSem.Value)
    (cut : DataSem.cutEnv live source.locals = some saved)
    (nextFree trigger : BitVec 64)
    (nextStore : target.store.lookup .nextFree = some (.word nextFree))
    (triggerStore : target.store.lookup .triggerGC = some (.word trigger))
    (slow : Compiler.Encoders.Asm.wordCmpHOL .lower (trigger - nextFree) (makeSpaceRequest64 amount) = true) :
    ∃ targetNext,
      WordSemStateFiniteExact.evaluate (compileControl64 conf secn label (.makeSpace amount live)).1 target =
        WordSemStateFiniteExact.evaluate
          (.seq (.assign 1 (.const (makeSpaceRequest64 amount)))
            (.seq (.alloc 1 (adjustSets live)) (silentFfi conf 3 (adjustSets live)))) targetNext ∧
      stateRel64 conf l1 l2 { source with locals := saved } targetNext none locs ∧
      DataSem.cutEnv live saved = some saved := by
  let initial := WordSemStateFiniteExact.setVar 1 (.word (trigger - nextFree)) target
  have initialRel := stateRel64_setScratch1 conf l1 l2 source target locs related (.word (trigger - nextFree))
  obtain ⟨after, run, afterRel⟩ := silentFfi64_related_fromState conf l1 l2 source initial locs initialRel live saved cut
  have clocks : initial.clock = after.clock := by
    exact initialRel.2.1.trans afterRel.2.1.symm
  let next := { after with clock := (if initial.clock < after.clock then initial.clock else after.clock), termdep := initial.termdep }
  have nextRel : stateRel64 conf l1 l2 { source with locals := saved } next none locs := by
    simpa [next, clocks, stateRel64] using afterRel
  refine ⟨next, ?_, nextRel, cutEnv_repeat live source.locals saved cut⟩
  rw [makeSpace64_slow_transition conf secn label target amount live nextFree trigger nextStore triggerStore slow]
  change WordSemStateFiniteExact.evaluate (.seq (silentFfi conf 3 (adjustSets live))
    (.seq (.assign 1 (.const (makeSpaceRequest64 amount)))
      (.seq (.alloc 1 (adjustSets live)) (silentFfi conf 3 (adjustSets live))))) initial = _
  simp only [WordSemStateFiniteExact.evaluate, run, WordSemStateFiniteExact.fixClock]
  rfl

/-- The diagnostic-independent slow path supplies the real allocator with
its proved collector result. The post-allocation diagnostic remains in the
executed continuation and is not discharged by this intermediate theorem. -/
theorem makeSpace64_slow_collector {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (amount : Nat) (live : NumSet) (saved : Spt DataSem.Value)
    (cut : DataSem.cutEnv live source.locals = some saved)
    (nextFree trigger : BitVec 64)
    (nextStore : target.store.lookup .nextFree = some (.word nextFree))
    (triggerStore : target.store.lookup .triggerGC = some (.word trigger))
    (slow : Compiler.Encoders.Asm.wordCmpHOL .lower (trigger - nextFree) (makeSpaceRequest64 amount) = true) :
    ∃ entry sourceNext targetNext enough,
      WordSemStateFiniteExact.evaluate (compileControl64 conf secn label (.makeSpace amount live)).1 target =
        WordSemStateFiniteExact.evaluate
          (.seq (.assign 1 (.const (makeSpaceRequest64 amount)))
            (.seq (.alloc 1 (adjustSets live)) (silentFfi conf 3 (adjustSets live)))) entry ∧
      WordSemStateFiniteExact.alloc (gcAllocSize amount) (adjustSets live)
        (WordSemStateFiniteExact.setVar 1 (.word (makeSpaceRequest64 amount)) entry) =
        (if enough then (none, targetNext) else (some .notEnoughSpace, WordSemStateFiniteExact.flushState true targetNext)) ∧
      stateRel64 conf l1 l2 sourceNext targetNext none locs ∧
      sourceNext.locals = saved ∧ sourceNext.stack = source.stack ∧ sourceNext.space = 0 ∧
      (enough = true → stateRel64 conf l1 l2 (DataSem.addSpace { source with locals := saved } amount) targetNext none locs) := by
  obtain ⟨entry, execution, entryRel, repeated⟩ := makeSpace64_slow_enterAllocator conf secn label l1 l2
    source target locs related amount live saved cut nextFree trigger nextStore triggerStore slow
  let prepared := WordSemStateFiniteExact.setVar 1 (.word (makeSpaceRequest64 amount)) entry
  have preparedRel := stateRel64_setScratch1 conf l1 l2 { source with locals := saved } entry locs entryRel (.word (makeSpaceRequest64 amount))
  obtain ⟨sourceNext, targetNext, enough, alloc, resultRel, localsEq, stackEq, spaceEq,
    _, _, _, _, _, reserved, _⟩ := stateRel64_alloc conf l1 l2 amount
      { source with locals := saved } prepared locs preparedRel live saved repeated
  refine ⟨entry, sourceNext, targetNext, enough, execution, ?_, resultRel, localsEq, stackEq, spaceEq, ?_⟩
  · simpa [prepared, makeSpaceRequest64_eq_gcAllocSize] using alloc
  · simpa using reserved

/-- Flapjack infrastructure: after cutting locals, source heap sizing can use
the collector proof's explicit default global root. -/
theorem sizeOfHeap_cut_roots {C F : Type} (source : DataSem.State C F) (saved : Spt DataSem.Value) :
    DataSem.sizeOfHeap { source with locals := saved } =
      (DataSem.sizeOfValues source.limits
        (sptToList saved ++ source.stack.flatMap DataSem.extractStack ++ [theGlobal source.global])
        source.refs .ln).1 := by
  unfold DataSem.sizeOfHeap DataSem.stackToValues
  simp only
  rw [sizeOfValues_global]

/-- Flapjack infrastructure: the failed collector bound makes the source
`addSpace` state unsafe, whether because of a thunk or excessive heap size. -/
theorem makeSpace_failure_unsafe {C F : Type} (source : DataSem.State C F)
    (saved : Spt DataSem.Value) (amount : Nat)
    (bound : DataSem.noThunksInRefs source.refs →
      source.limits.heapLimit <
        (DataSem.sizeOfValues source.limits
          (sptToList saved ++ source.stack.flatMap DataSem.extractStack ++ [theGlobal source.global])
          source.refs .ln).1 + amount) :
    (DataSem.addSpace { source with locals := saved } amount).safeForSpace = false := by
  by_cases noThunks : DataSem.noThunksInRefs source.refs
  · have tooLarge := bound noThunks
    simp only [DataSem.addSpace]
    rw [sizeOfHeap_cut_roots]
    simp
    intro _ _
    simpa only [List.append_assoc] using tooLarge
  · simp [DataSem.addSpace, noThunks]

/-- Flapjack infrastructure: the slow compiled path preserves the relation
on success after the evaluator's clock clamp; a failed active collection makes
the source `makeSpace` result unsafe. -/
theorem makeSpace64_slow_branches {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (amount : Nat) (live : NumSet) (saved : Spt DataSem.Value)
    (cut : DataSem.cutEnv live source.locals = some saved)
    (nextFree trigger : BitVec 64)
    (nextStore : target.store.lookup .nextFree = some (.word nextFree))
    (triggerStore : target.store.lookup .triggerGC = some (.word trigger))
    (slow : Compiler.Encoders.Asm.wordCmpHOL .lower (trigger - nextFree) (makeSpaceRequest64 amount) = true)
    (noFfi : conf.callEmptyFfi = false) :
    let prepared := WordSemStateFiniteExact.setVar 1 (.word (makeSpaceRequest64 amount))
      (WordSemStateFiniteExact.setVar 1 (.word (trigger - nextFree)) target)
    ∃ (sourceNext : DataSem.State C F) (targetNext : WordSemStateFiniteExact 64 C F) (enough : Bool),
      WordSemStateFiniteExact.evaluate (compileControl64 conf secn label (.makeSpace amount live)).1 target =
        WordSemStateFiniteExact.fixClock prepared
          (if enough then (none, targetNext) else (some .notEnoughSpace, WordSemStateFiniteExact.flushState true targetNext)) ∧
      (enough = true → continues64 conf secn label l1 l2 (.makeSpace amount live) source target locs) ∧
      (enough = true →
        WordSemStateFiniteExact.evaluate (compileControl64 conf secn label (.makeSpace amount live)).1 target =
          (none, { targetNext with clock := min prepared.clock targetNext.clock, termdep := prepared.termdep }) ∧
        stateRel64 conf l1 l2
          { sourceNext with space := amount, clock := min prepared.clock targetNext.clock }
          { targetNext with clock := min prepared.clock targetNext.clock, termdep := prepared.termdep } none locs) ∧
      (enough = false → conf.gcKind ≠ .none →
        (WordSemStateFiniteExact.evaluate (compileControl64 conf secn label (.makeSpace amount live)).1 target).1 =
          some .notEnoughSpace ∧
        (DataSem.addSpace { source with locals := saved } amount).safeForSpace = false) := by
  let prepared := WordSemStateFiniteExact.setVar 1 (.word (makeSpaceRequest64 amount))
    (WordSemStateFiniteExact.setVar 1 (.word (trigger - nextFree)) target)
  obtain ⟨sourceNext, targetNext, enough, run, _, _, _, _, reserve, originalReserve, failed⟩ :=
    makeSpace64_slow_allocator conf secn label l1 l2 source target locs related amount live saved cut
      nextFree trigger nextStore triggerStore slow noFfi
  refine ⟨sourceNext, targetNext, enough, run, ?_, ?_, ?_⟩
  · intro yes
    have finalRel := originalReserve yes
    have clockEq : targetNext.clock = prepared.clock := by
      simpa [prepared, WordSemStateFiniteExact.setVar, DataSem.addSpace, related.2.1] using finalRel.2.1
    let finalTarget := { targetNext with termdep := prepared.termdep }
    have fixed : WordSemStateFiniteExact.fixClock prepared ((none : Option (WordSemResult 64)), targetNext) =
        (none, finalTarget) := by
      simp [WordSemStateFiniteExact.fixClock, finalTarget, clockEq]
    have targetRun : WordSemStateFiniteExact.evaluate (compileControl64 conf secn label (.makeSpace amount live)).1 target =
        (none, finalTarget) := by
      change WordSemStateFiniteExact.evaluate (compileControl64 conf secn label (.makeSpace amount live)).1 target =
        WordSemStateFiniteExact.fixClock prepared
          (if enough then (none, targetNext) else (some .notEnoughSpace, WordSemStateFiniteExact.flushState true targetNext)) at run
      simpa only [yes, ↓reduceIte, fixed] using run
    refine ⟨DataSem.addSpace { source with locals := saved } amount, finalTarget, ?_, targetRun, ?_⟩
    · simp [DataSem.evaluate, cut]
    · simpa [stateRel64, finalTarget] using finalRel
  · intro yes
    have clockEq : (if prepared.clock < targetNext.clock then prepared.clock else targetNext.clock) =
        min prepared.clock targetNext.clock := by split <;> omega
    refine ⟨?_, ?_⟩
    · change WordSemStateFiniteExact.evaluate (compileControl64 conf secn label (.makeSpace amount live)).1 target =
          WordSemStateFiniteExact.fixClock prepared
            (if enough then (none, targetNext) else (some .notEnoughSpace, WordSemStateFiniteExact.flushState true targetNext)) at run
      simpa only [yes, ↓reduceIte, WordSemStateFiniteExact.fixClock, clockEq] using run
    have aligned := stateRel64_withClock conf l1 l2 { sourceNext with space := amount } targetNext none locs
      (min prepared.clock targetNext.clock) (reserve yes)
    · simpa [stateRel64] using aligned
  · intro no active
    refine ⟨?_, ?_⟩
    · have result := congrArg Prod.fst run
      simpa [no, WordSemStateFiniteExact.fixClock] using result
    apply makeSpace_failure_unsafe source saved amount
    intro noThunks
    apply failed no active noThunks
      (sptToList saved ++ source.stack.flatMap DataSem.extractStack ++ [theGlobal source.global]) []
    · simp
    · simp

/-- Flapjack infrastructure: with an active collector and a source result
that remains space-safe, the compiled slow allocation path continues with
the actual source `makeSpace` state related to the word result. -/
theorem makeSpace64_slow_continues {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (amount : Nat) (live : NumSet) (saved : Spt DataSem.Value)
    (cut : DataSem.cutEnv live source.locals = some saved)
    (nextFree trigger : BitVec 64)
    (nextStore : target.store.lookup .nextFree = some (.word nextFree))
    (triggerStore : target.store.lookup .triggerGC = some (.word trigger))
    (slow : Compiler.Encoders.Asm.wordCmpHOL .lower (trigger - nextFree) (makeSpaceRequest64 amount) = true)
    (noFfi : conf.callEmptyFfi = false) (active : conf.gcKind ≠ .none)
    (safe : (DataSem.addSpace { source with locals := saved } amount).safeForSpace = true) :
    continues64 conf secn label l1 l2 (.makeSpace amount live) source target locs := by
  obtain ⟨_, _, enough, _, success, _, failure⟩ :=
    makeSpace64_slow_branches conf secn label l1 l2 source target locs related amount live saved cut
      nextFree trigger nextStore triggerStore slow noFfi
  cases flag : enough with
  | true => exact success flag
  | false =>
    have unsafeResult := (failure flag active).2
    rw [safe] at unsafeResult
    contradiction

/-- Flapjack infrastructure: both the fast check and the collection path
simulate a space-safe source command for an active collector when diagnostic
FFIs are disabled. -/
theorem makeSpace64_continues {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (amount : Nat) (live : NumSet) (saved : Spt DataSem.Value)
    (cut : DataSem.cutEnv live source.locals = some saved)
    (noFfi : conf.callEmptyFfi = false) (active : conf.gcKind ≠ .none)
    (safe : (DataSem.addSpace { source with locals := saved } amount).safeForSpace = true) :
    continues64 conf secn label l1 l2 (.makeSpace amount live) source target locs := by
  obtain ⟨nextFree, trigger, _, nextStore, triggerStore, _, _, _, _⟩ :=
    stateRel64_spaceAvailable conf l1 l2 source target locs related
  cases branch : Compiler.Encoders.Asm.wordCmpHOL .lower (trigger - nextFree) (makeSpaceRequest64 amount) with
  | false =>
    exact makeSpace64_fast conf secn label l1 l2 source target locs related amount live saved cut
      ⟨nextFree, trigger, nextStore, triggerStore, branch⟩
  | true =>
    exact makeSpace64_slow_continues conf secn label l1 l2 source target locs related amount live saved cut
      nextFree trigger nextStore triggerStore branch noFfi active safe

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
