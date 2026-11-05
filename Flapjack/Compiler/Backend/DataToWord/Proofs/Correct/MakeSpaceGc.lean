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

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
