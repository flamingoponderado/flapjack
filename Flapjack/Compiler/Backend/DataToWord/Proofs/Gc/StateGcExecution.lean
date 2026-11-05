import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.WordGcCorrect
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.RootsValid
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CollectorStore
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CallEnv

/-! Executing collection from the data-to-word state relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions

/-- Flapjack infrastructure: with no live source locals, the candidate state
relation supplies a successful collector execution, a decoded related stack,
and the output memory relation at zero required space. -/
theorem stateRel64_gc_execute {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (emptyLocals : source.locals = .ln) :
    ∃ moved memory store stack,
      target.gcFun (wordSemEncStack target.stack, target.memory, target.mdomain, target.store) =
        some (moved, memory, store) ∧
      wordSemDecStack moved target.stack = some stack ∧
      List.Forall₂ stackRel source.stack stack ∧ List.Forall₂ containsLoc stack locs ∧
      Memory.memoryRel conf target.be (holThe source.tstamps) source.refs 0 store memory target.mdomain
        ([(theGlobal source.global, holFapply store .globals)] ++ flatStack source.stack stack) ∧
      store.lookup (.temp 29) = target.store.lookup (.temp 29) ∧
      store.lookup .allocSize = target.store.lookup .allocSize ∧
      store.lookup .heapLength = target.store.lookup .heapLength := by
  have gcEq := related.2.2.2.1
  have good := related.2.2.2.2.2.2.1
  have memoryRel := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨heap, limit, a, sp, sp1, gens, heapMem, inv, limitBound, spaceBound⟩ := memoryRel
  have emptyInter : sptInter target.locals (adjustSet source.locals) = .ln := by
    rw [emptyLocals]
    cases target.locals <;> simp [adjustSet, sptFromAList, sptInter]
  have normalized : Memory.wordMlInv (heap, target.be, a, sp, sp1, gens) limit (holThe source.tstamps)
      conf source.refs ((theGlobal source.global, holFapply target.store .globals) :: flatStack source.stack target.stack) := by
    simpa [emptyInter, joinEnv] using inv
  obtain ⟨roots, heap1, gens1, a1, n1, moved, memory, store, free1, free2,
    run, heapOut, wordOut, _, sum, length, full, rootRel, enough, zero, allocation⟩ :=
    wordGc_combined_memory conf (theGlobal source.global) (flatStack source.stack target.stack) source.refs
      heap target.be a sp sp1 limit (holThe source.tstamps) gens target.store target.memory target.mdomain normalized good heapMem
  have runTarget : target.gcFun (wordSemEncStack target.stack, target.memory, target.mdomain, target.store) =
      some (moved, memory, store) := by
    rw [gcEq, ← flatStack_values_eq_encStack source.stack target.stack related.2.2.2.2.2.2.2.2.2.2.2.2.1]
    exact run
  obtain ⟨stack, decoded, stackRel, locRel, flat⟩ := stateRel64_gc_decode conf l1 l2 source target locs related moved memory store runTarget
  have wordOut' : Memory.wordMlInv (heap1, target.be, a1, free1, free2, gens1) limit (holThe source.tstamps)
      conf source.refs ((theGlobal source.global, holFapply store .globals) :: flatStack source.stack stack) := by
    simpa [flat] using wordOut
  have memoryOut : Memory.memoryRel conf target.be (holThe source.tstamps) source.refs 0 store memory target.mdomain
      ([(theGlobal source.global, holFapply store .globals)] ++ flatStack source.stack stack) := by
    exact ⟨heap1, limit, a1, free1, free2, gens1, heapOut, wordOut', limitBound, Nat.zero_le _⟩
  have storeFacts := wordGcFun_store_invariants conf _ moved target.memory memory target.mdomain target.store store (by simpa [gcEq] using runTarget)
  exact ⟨moved, memory, store, stack, runTarget, decoded, stackRel, locRel, memoryOut,
    storeFacts.2.2.2.2.2.2.1, storeFacts.1, storeFacts.2.2.2.2.2.2.2.1⟩

/-- Flapjack infrastructure: executing the production collector from the
64-bit candidate relation preserves that relation with zero required space.
The candidate code/oracle relation has not yet been shown equivalent to HOL's
unrestricted compiler relation. -/
theorem stateRel64_gc_preserved {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (emptyLocals : source.locals = .ln) :
    ∃ moved memory store stack,
      target.gcFun (wordSemEncStack target.stack, target.memory, target.mdomain, target.store) =
        some (moved, memory, store) ∧
      wordSemDecStack moved target.stack = some stack ∧
      store.lookup (.temp 29) = target.store.lookup (.temp 29) ∧
      store.lookup .allocSize = target.store.lookup .allocSize ∧
      stateRel64 conf l1 l2 { source with space := 0 }
        { target with stack := stack, store := store, memory := memory } none locs := by
  obtain ⟨moved, memory, store, stack, run, decoded, newStackRel, newLocs, memoryOut, temp, alloc, heapLength⟩ :=
    stateRel64_gc_execute conf l1 l2 source target locs related emptyLocals
  have gcEq := related.2.2.2.1
  have storeFacts := wordGcFun_store_invariants conf _ moved target.memory memory target.mdomain target.store store (by simpa [gcEq] using run)
  rcases related with ⟨ffi, clock, handler, gcFun, code, oracle, good, shift, timestamps, globals, localZero,
    names, oldStackRel, _, stackBound, stackMax, stackSize, localsSize, limits, _⟩
  have newOracle : codeOracleRel64 conf source.compile source.compileOracle store target.compile target.compileOracle
      target.codeBuffer target.dataBuffer := by
    simpa [codeOracleRel64, storeFacts.2.2.1, storeFacts.2.2.2.1, storeFacts.2.2.2.2.1,
      storeFacts.2.2.2.2.2.1] using oracle
  have stackEq : wordSemStackSize stack = wordSemStackSize target.stack :=
    (stackRel_sizeOfStack newStackRel).trans (stackRel_sizeOfStack oldStackRel).symm
  have emptyInter : sptInter target.locals (adjustSet source.locals) = .ln := by
    rw [emptyLocals]
    cases target.locals <;> simp [adjustSet, sptFromAList, sptInter]
  refine ⟨moved, memory, store, stack, run, decoded, temp, alloc, ?_⟩
  refine ⟨ffi, clock, handler, gcFun, code, newOracle, good, shift, timestamps, ?_, localZero,
    names, newStackRel, newLocs, ?_, stackMax, stackSize, localsSize, ?_, ?_⟩
  · exact Option.isSome_iff_ne_none.mp storeFacts.2.2.2.2.2.2.2.2
  · simpa [stackEq] using stackBound
  · simpa [heapLength] using limits
  · simpa [emptyInter, joinEnv] using memoryOut

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
