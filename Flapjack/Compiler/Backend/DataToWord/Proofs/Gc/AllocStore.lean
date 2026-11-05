import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.HasSpace

/-! The allocation request store slot does not affect the state relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend

/-- Flapjack infrastructure: writing the allocator's request leaves all
heap, compiler, and stack components of the candidate relation intact. -/
theorem stateRel64_setAllocSize {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (request : BitVec 64) :
    stateRel64 conf l1 l2 source (WordSemStateFiniteExact.setStore .allocSize (.word request) target) none locs := by
  rcases related with ⟨ffi, clock, handler, gc, code, oracle, good, shift, stamps, globals, zero,
    names, stackRel, locRel, stackBound, stackMax, stackSize, localsSize, limits, memory⟩
  have globalsApply : holFapply (target.store.updateEq (.allocSize, .word request)) .globals =
      holFapply target.store .globals := by
    simp [holFapply, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
  have newOracle : codeOracleRel64 conf source.compile source.compileOracle
      (target.store.updateEq (.allocSize, .word request)) target.compile target.compileOracle
      target.codeBuffer target.dataBuffer := by
    simpa [codeOracleRel64, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using oracle
  have newLimits : limitsInv source.limits ((target.store.updateEq (.allocSize, .word request)).lookup .heapLength)
      target.stackLimit conf.lenSize conf.hasFpOps conf.hasFpTern := by
    simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using limits
  obtain ⟨heap, limit, a, sp, sp1, gens, heapMem, wordInv, limitBound, spaceBound⟩ := memory
  have newHeap : Memory.heapInMemoryStore heap a sp sp1 gens conf
      (target.store.updateEq (.allocSize, .word request)) target.memory target.mdomain limit := by
    simpa [Memory.heapInMemoryStore, Memory.globRealInv, Memory.genStartsInStore,
      HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using heapMem
  have newMemory : Memory.memoryRel conf target.be (holThe source.tstamps) source.refs source.space
      (target.store.updateEq (.allocSize, .word request)) target.memory target.mdomain
      (joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
        [(theGlobal source.global, holFapply (target.store.updateEq (.allocSize, .word request)) .globals)] ++
        flatStack source.stack target.stack) := by
    rw [globalsApply]
    exact ⟨heap, limit, a, sp, sp1, gens, newHeap, wordInv, limitBound, spaceBound⟩
  refine ⟨ffi, clock, handler, gc, code, newOracle, good, shift, stamps, ?_, zero,
    names, stackRel, locRel, stackBound, stackMax, stackSize, localsSize, newLimits, ?_⟩
  · simpa [WordSemStateFiniteExact.setStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using globals
  · simpa [WordSemStateFiniteExact.setStore] using newMemory

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
