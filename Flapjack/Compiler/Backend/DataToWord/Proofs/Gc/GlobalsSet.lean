import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GlobalStore
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.GlobalsSet

/-! Changing the active global pointer in the production state relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- Installing a related immutable reference as the global pointer updates
both target store entries and preserves the production-backed state relation. -/
theorem stateRel64_installGlobals {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (name ptr : Nat) (sourceRun : DataSem.getVar name source.locals = some (.refPtr true ptr)) :
    ∃ word addr,
      WordSemStateFiniteExact.getVar (adjustVar name) target = some (.word word) ∧
      WordSemStateFiniteExact.wordExp
        (WordSemStateFiniteExact.setStore .globals (.word word) target) (realAddr conf (adjustVar name)) =
          some (.word addr) ∧
      stateRel64 conf l1 l2 { source with global := some ptr }
        (WordSemStateFiniteExact.setStore .globReal (.word addr)
          (WordSemStateFiniteExact.setStore .globals (.word word) target)) none locs := by
  obtain ⟨location, wordRun⟩ := stateRel64_getVar conf l1 l2 source target none locs related name (.refPtr true ptr) sourceRun
  have member := localPair_mem_joinEnv source.locals target.locals name (.refPtr true ptr) location sourceRun wordRun
  have shiftBound : shiftLength conf < 64 := related.2.2.2.2.2.2.2.1
  have memory := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  let roots := joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
    [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack
  have focused : Memory.memoryRel conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain ((.refPtr true ptr, location) :: roots) := by
    apply Memory.memoryRel_rearrange conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain roots
    · intro pair present
      simp only [List.mem_cons] at present
      rcases present with rfl | tail
      · exact List.mem_append_left _ (List.mem_append_left _ member)
      · exact tail
    · simpa [roots] using memory
  obtain ⟨word, addr, locationEq, real, simple⟩ :=
    Memory.memoryRel_refPtrTrueAddress conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain ptr location roots (Or.inr rfl) focused
  have targetRun : WordSemStateFiniteExact.getVar (adjustVar name) target = some (.word word) := by
    simpa [locationEq] using wordRun
  let target1 := WordSemStateFiniteExact.setStore .globals (.word word) target
  let target2 := WordSemStateFiniteExact.setStore .globReal (.word addr) target1
  have addrRun1 : WordSemStateFiniteExact.wordExp target1 (realAddr conf (adjustVar name)) = some (.word addr) := by
    apply wordExp_realAddr64 conf target1 (adjustVar name) word addr shiftBound
    · simpa [target1, WordSemStateFiniteExact.setStore, WordSemStateFiniteExact.getVar] using targetRun
    · simpa [target1, WordSemStateFiniteExact.setStore, Memory.getRealAddr,
        HolFiniteMapExact.updateEq, FUPDATE_HOL] using real
  refine ⟨word, addr, targetRun, addrRun1, ?_⟩
  have rearranged : Memory.memoryRel conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain
      (joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
        [(.refPtr true ptr, .word word)] ++ flatStack source.stack target.stack) := by
    apply Memory.memoryRel_rearrange conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain roots
    · intro pair present
      simp only [List.mem_append, List.mem_singleton] at present ⊢
      have pairMember : (DataSem.Value.refPtr true ptr, .word word) ∈
          joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) := by
        simpa [locationEq] using member
      aesop
    · simpa [roots] using memory
  have updated := Memory.memoryRel_setGlobals conf target.be (holThe source.tstamps) source.refs source.space
    target.store target.memory target.mdomain _ word addr simple rearranged
  rcases related with ⟨ffi, clock, handler, gc, code, oracle, good, shift, stamps, globals, zero,
    names, stackRel, locRel, stackBound, stackMax, stackSize, localsSize, limits, _⟩
  refine ⟨ffi, clock, handler, gc, code, ?_, good, shift, stamps, ?_, zero,
    names, stackRel, locRel, stackBound, stackMax, stackSize, localsSize, ?_, ?_⟩
  · simpa [target2, target1, WordSemStateFiniteExact.setStore, codeOracleRel64,
      HolFiniteMapExact.updateEq, FUPDATE_HOL] using oracle
  · simp [WordSemStateFiniteExact.setStore, HolFiniteMapExact.updateEq, FUPDATE_HOL]
  · simpa [target2, target1, WordSemStateFiniteExact.setStore, HolFiniteMapExact.updateEq, FUPDATE_HOL] using limits
  · simpa [target2, target1, WordSemStateFiniteExact.setStore, HolFiniteMapExact.updateEq, FUPDATE_HOL,
      holFapply_of_lookup, theGlobal] using updated

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
