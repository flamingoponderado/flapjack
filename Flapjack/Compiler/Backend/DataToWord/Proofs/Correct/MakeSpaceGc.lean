import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.MakeSpaceSlow
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
    _, _, reserve, failed⟩ := stateRel64_alloc conf l1 l2 amount source prepared locs preparedRel live saved cut
  refine ⟨sourceNext, targetNext, enough, ?_, nextRel, sourceLocals, sourceStack, sourceSpace, reserve, failed⟩
  rw [makeSpace64_slow_noFfi conf secn label target amount live nextFree trigger nextStore triggerStore slow noFfi]
  change WordSemStateFiniteExact.fixClock prepared
    (WordSemStateFiniteExact.evaluate (.alloc 1 (adjustSets live)) prepared) = _
  have read : WordSemStateFiniteExact.getVar 1 prepared = some (.word (makeSpaceRequest64 amount)) := by
    simp [prepared, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
  simp only [WordSemStateFiniteExact.evaluate, read, makeSpaceRequest64_eq_gcAllocSize, alloc]
  simp only [prepared, makeSpaceRequest64_eq_gcAllocSize]

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
  obtain ⟨sourceNext, targetNext, enough, run, _, _, _, _, reserve, failed⟩ :=
    makeSpace64_slow_allocator conf secn label l1 l2 source target locs related amount live saved cut
      nextFree trigger nextStore triggerStore slow noFfi
  refine ⟨sourceNext, targetNext, enough, run, ?_, ?_⟩
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

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
