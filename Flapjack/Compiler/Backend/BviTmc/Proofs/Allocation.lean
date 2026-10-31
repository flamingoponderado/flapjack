import Flapjack.Compiler.Backend.BviTmc.Proofs.StateRelation
import Flapjack.Compiler.Backend.BviTmc.Proofs.HoleRelation

/-! Preservation of the TMC state relation under fresh allocation. -/
namespace Flapjack.Compiler.Backend.BviTmc
open BvlSem BviSem

namespace AllocationWitness
theorem holFmapAsFiniteSupportRelationWitness_BviState {C F : Type} :
    (∀ s : BviStateBroad C F, (BviState.ofBroad s).toBroad = s) ∧
      (∀ s : BviState C F, BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness
end AllocationWitness

/-- Allocating related cells at fresh pointers preserves the state relation,
extends the pointer map, and preserves existing mutable holes. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "state_rel_alloc"
  (fmap_as_finite_support_relation := [BviState.refs, f])]
theorem stateRel_alloc {C F : Type} (f : HolFiniteMapExact Nat Nat)
    (source : BviState (Nat × C) F) (target : BviState C F) (src tgt : Nat) (v w : Ref Value)
    (related : stateRel f source target) (srcFresh : src ∉ source.refs.domain)
    (tgtFresh : tgt ∉ target.refs.domain) (rangeFresh : tgt ∉ mapRange f)
    (cells : refRel (f.updateEq (src, tgt)) v w) :
    (f.updateEq (src, tgt)).lookup src = some tgt ∧
    stateRel (f.updateEq (src, tgt)) { source with refs := source.refs.updateEq (src, v) }
      { target with refs := target.refs.updateEq (tgt, w) } ∧
    finiteSubmap f (f.updateEq (src, tgt)) ∧ onlyFresh f (f.updateEq (src, tgt)) target.refs ∧
    holesUnchangedExcept f target.refs (target.refs.updateEq (tgt, w)) ∅ ∧
    holesStillNotFinalised f target.refs (target.refs.updateEq (tgt, w)) := by
  have mapMissing : f.lookup src = none := by
    have absent : src ∉ f.domain := by rw [related.1.1]; exact srcFresh
    simpa [HolFiniteMapExact.domain] using absent
  have extension : finiteSubmap f (f.updateEq (src, tgt)) := by
    intro i j found
    have ne : i ≠ src := by
      intro eq
      subst i
      rw [mapMissing] at found
      contradiction
    simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, ne] using found
  have notRange : ∀ i, f.lookup i ≠ some tgt := by
    intro i found
    exact rangeFresh ⟨i, found⟩
  have tgtMissing : target.refs.lookup tgt = none := by
    simpa [HolFiniteMapExact.domain] using tgtFresh
  refine ⟨by simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL], ?_, extension, ?_, ?_, ?_⟩
  · rcases related with ⟨heap, clock, global, ffi, oracle, compiler, code, names, inputs, workers, inj⟩
    refine ⟨stateRefRel_alloc f source.refs target.refs src tgt v w heap srcFresh tgtFresh notRange cells,
      clock, ?_, ffi, oracle, compiler, code, names, inputs, workers, fmapInj_update f src tgt inj notRange⟩
    cases hs : source.global <;> cases ht : target.global <;> simp_all
    exact extension _ _ global
  · intro ptr ⟨⟨key, lookup⟩, outside⟩
    by_cases eq : key = src
    · subst key
      simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at lookup
      subst ptr
      exact tgtFresh
    · have oldLookup : f.lookup key = some ptr := by
        simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, eq] using lookup
      exact (outside ⟨key, oldLookup⟩).elim
  · intro ptr tag finalised left child right _ found
    have ne : ptr ≠ tgt := by
      intro eq
      subst ptr
      rw [tgtMissing] at found
      contradiction
    exact ⟨finalised, child, by simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, ne] using found,
      fun _ => rfl⟩
  · intro ptr _ ⟨tag, left, child, right, found⟩
    have ne : ptr ≠ tgt := by
      intro eq
      subst ptr
      rw [tgtMissing] at found
      contradiction
    exact ⟨tag, left, child, right, by
      simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, ne] using found⟩

end Flapjack.Compiler.Backend.BviTmc
