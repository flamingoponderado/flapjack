import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CutEnv
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Space

/-! Source environment cuts and reserved space in the state relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- Cutting source locals while keeping target locals retains the relation:
every surviving source/target root pair was already present. -/
theorem stateRel64_sourceCut {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (live : NumSet) (saved : Spt DataSem.Value) (cut : DataSem.cutEnv live source.locals = some saved) :
    stateRel64 conf l1 l2 { source with locals := saved } target none locs := by
  rcases related with ⟨ffi, clock, handler, gc, code, oracle, good, shift, stamps, globals, zero,
    names, stackRel, locRel, stackBound, stackMax, stackSize, localsSize, limits, memory⟩
  refine ⟨ffi, clock, handler, gc, code, oracle, good, shift, stamps, globals, zero,
    ?_, stackRel, locRel, stackBound, stackMax, stackSize, localsSize, limits, ?_⟩
  · intro n present
    obtain ⟨value, lookup⟩ := Option.isSome_iff_exists.mp present
    have oldLookup := cutEnv_lookup_retained live source.locals saved cut n value lookup
    exact names n (by simp [oldLookup])
  · apply Memory.memoryRel_rearrange conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain
      (joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
        [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack)
    · intro pair member
      simp only [Option.getD_none, List.nil_append] at member
      simp only [List.mem_append, List.mem_singleton] at member ⊢
      rcases member with (localMember | globalMember) | stackMember
      · exact Or.inl (Or.inl (joinEnv_cutEnv_mem_general pair target.locals live source.locals saved localMember cut))
      · exact Or.inl (Or.inr globalMember)
      · exact Or.inr stackMember
    · simpa using memory

/-- The target allocation and collection pointers determine a maximum source
reservation; any amount within it preserves the state relation. -/
theorem stateRel64_spaceAvailable {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs) :
    ∃ nextFree trigger available,
      target.store.lookup .nextFree = some (.word nextFree) ∧
      target.store.lookup .triggerGC = some (.word trigger) ∧
      trigger - nextFree = 8 * BitVec.ofNat 64 available ∧
      source.space ≤ available ∧ 8 * available < 2 ^ 64 ∧
      ∀ amount, amount ≤ available → stateRel64 conf l1 l2 { source with space := amount } target none locs := by
  have memory := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨nextFree, trigger, available, nextStore, triggerStore, difference, availableBound, full, bounded⟩ :=
    Memory.memoryRel_spaceMax conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain _ memory
  refine ⟨nextFree, trigger, available, nextStore, triggerStore, ?_, availableBound, ?_, ?_⟩
  · simpa [StackRemove.bytesInWord] using difference
  · simpa using bounded (Or.inr rfl)
  · intro amount within
    have smaller := Memory.memoryRel_lessSpace conf target.be (holThe source.tstamps) source.refs available amount
      target.store target.memory target.mdomain _ ⟨full, within⟩
    rcases related with ⟨ffi, clock, handler, gc, code, oracle, good, shift, stamps, globals, zero,
      names, stackRel, locRel, stackBound, stackMax, stackSize, localsSize, limits, _⟩
    exact ⟨ffi, clock, handler, gc, code, oracle, good, shift, stamps, globals, zero,
      names, stackRel, locRel, stackBound, stackMax, stackSize, localsSize, limits, smaller⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
