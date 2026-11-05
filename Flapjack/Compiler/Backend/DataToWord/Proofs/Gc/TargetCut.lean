import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.MakeSpace
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.Scratch
import Flapjack.Compiler.Backend.DataSpace.Proofs.Cuts

/-! Restricting both local environments after the diagnostic call. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- Flapjack simulation infrastructure: cutting the source locals and the
word locals to the corresponding live sets preserves the candidate relation.
The word cut retains register zero as well as the adjusted live locals. -/
theorem stateRel64_cutBoth {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (live : NumSet) (saved : Spt DataSem.Value)
    (cut : DataSem.cutEnv live source.locals = some saved) :
    stateRel64 conf l1 l2 { source with locals := saved }
      { target with locals := (sptUnion (sptInter target.locals (adjustSet live))
          (sptInter target.locals (.ls ()))) } none locs := by
  let kept := sptUnion (sptInter target.locals (adjustSet live)) (sptInter target.locals (.ls ()))
  have retained (n : Nat) (value : DataSem.Value) (lookup : sptLookup n saved = some value) :
      sptLookup (adjustVar n) kept = sptLookup (adjustVar n) target.locals := by
    have liveLookup : (sptLookup n live).isSome = true := by
      rw [cutEnv_saved_eq live source.locals saved cut, sptLookup_mkWf, sptLookup_sptInterCases] at lookup
      cases h : sptLookup n live <;> simp_all
    have adj : sptLookup (adjustVar n) (adjustSet live) = some () := by
      rw [lookup_adjustSet_map]
      cases h : sptLookup n live <;> simp_all
    cases h : sptLookup (adjustVar n) target.locals <;>
      simp [kept, sptLookup_sptUnion, sptLookup_sptInterCases, adj, h]
  have zero : sptLookup 0 kept = sptLookup 0 target.locals := by
    cases h : sptLookup 0 target.locals <;> cases h2 : sptLookup 0 (adjustSet live) <;>
      simp [kept, sptLookup_sptUnion, sptLookup_sptInterCases, sptLookup, h, h2]
  have base := stateRel64_sourceCut conf l1 l2 source target locs related live saved cut
  rcases base with ⟨ffi, clock, handler, gc, code, oracle, good, shift, stamps, globals, zeroRel,
    names, stackRel, locRel, stackBound, stackMax, stackSize, localsSize, limits, memory⟩
  refine ⟨ffi, clock, handler, gc, code, oracle, good, shift, stamps, globals, ?_,
    ?_, stackRel, locRel, stackBound, stackMax, stackSize, localsSize, limits, ?_⟩
  · intro h
    change sptLookup 0 kept = _
    rw [zero]
    exact zeroRel h
  · intro n present
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp present
    change (sptLookup (adjustVar n) kept).isSome = true
    rw [retained n v hv]
    exact names n present
  · apply Memory.memoryRel_rearrange conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain
      (joinEnv saved (sptToAList (sptInter target.locals (adjustSet saved))) ++
        [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack)
    · intro pair member
      simp only [Option.getD_none, List.nil_append, List.mem_append] at member ⊢
      rcases member with (localMember | globalMember) | stackMember
      · obtain ⟨n, hs, ht⟩ := joinEnv_localPair saved kept pair.1 pair.2 localMember
        rw [retained n pair.1 hs] at ht
        exact Or.inl (Or.inl (localPair_mem_joinEnv saved target.locals n pair.1 pair.2 hs ht))
      · exact Or.inl (Or.inr globalMember)
      · exact Or.inr stackMember
    · simpa using memory

/-- Repeating a successful source cut leaves its normalized result unchanged. -/
theorem cutEnv_repeat {α : Type} (live : NumSet) (source saved : Spt α)
    (cut : DataSem.cutEnv live source = some saved) :
    DataSem.cutEnv live saved = some saved := by
  classical
  have subset : ∀ key, sptMem key live → sptMem key source := by
    unfold DataSem.cutEnv at cut
    split at cut
    · assumption
    · contradiction
  have savedEq : saved = sptMkWf (sptInter source live) := by
    unfold DataSem.cutEnv at cut
    split at cut
    · simpa using cut.symm
    · contradiction
  have present : ∀ key, sptMem key live → sptMem key saved := by
    intro key member
    obtain ⟨v, hv⟩ := (sptMem_iff_lookup key source).mp (subset key member)
    obtain ⟨u, hu⟩ := (sptMem_iff_lookup key live).mp member
    apply (sptMem_iff_lookup key saved).mpr
    refine ⟨v, ?_⟩
    rw [savedEq, sptLookup_mkWf, sptLookup_sptInterCases, hv, hu]
  have same : sptMkWf (sptInter saved live) = saved := by
    apply (sptEqThm _ _ ⟨DataSpace.sptWf_normalize _, by
      rw [savedEq]; exact DataSpace.sptWf_normalize _⟩).2
    intro key
    rw [sptLookup_mkWf, sptLookup_sptInterCases, savedEq, sptLookup_mkWf,
      sptLookup_sptInterCases]
    cases sptLookup key source <;> cases sptLookup key live <;> rfl
  simp only [DataSem.cutEnv, if_pos present, same]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
