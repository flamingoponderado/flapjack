module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateRelation
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.StackPermute
@[expose] public section

/-! Global-pointer consequences of the data-to-word memory relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

namespace globalLookupMap
/-- Canonical target-state finite-map roundtrip. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end globalLookupMap

/-- A related state with a global reference stores its encoded address. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "state_rel_lookup_globals"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem stateRel_lookupGlobals {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (s : Flapjack.Compiler.Backend.DataSem.State C F)
    (t : WordSemStateFiniteExact width C F) (v : Option (List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)))
    (locs : List (Nat × Nat)) (g : Nat)
    (premises : stateRel conf l1 l2 s t v locs ∧ s.global = some g) :
    ∃ x u, t.store.lookup .globals = some (.word (getAddr conf x u)) := by
  obtain ⟨related, globalEq⟩ := premises
  rcases related with ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift,
    htstamp, hglobal, hzero, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, hmem⟩
  obtain ⟨heap, limit, a, sp, sp1, gens, hstore, hinv, hbound, hspace⟩ := hmem
  have singleton : wordMlInv (heap, t.be, a, sp, sp1, gens) limit (holThe s.tstamps) conf s.refs
      [(theGlobal s.global, holFapply t.store .globals)] := by
    apply wordMlInv_rearrange heap t.be a sp sp1 gens limit (holThe s.tstamps) conf s.refs _ _ ?_ hinv
    intro pair member
    simp only [List.mem_singleton] at member
    subst pair
    simp
  simp [theGlobal, globalEq] at singleton
  unfold wordMlInv at singleton
  obtain ⟨roots, abs, words⟩ := singleton
  simp only [List.map_cons, List.map_nil] at abs words
  cases words with
  | cons wordEq tail =>
    cases tail
    simp only [absMlInv, bcStackRefInv] at abs
    obtain ⟨rootsOk, heapOk, gcOk, unused, f, tf, injF, domF, injTf, domTf,
      timeBound, beOk, unique, values, refs⟩ := abs
    cases values with
    | cons valueRel tail =>
      have value0 := valueRel 0
      cases value0
      obtain ⟨value, found⟩ := Option.isSome_iff_exists.mp (hglobal .globals (by simp))
      have applyEq := holFapply_of_lookup found
      simp only [wordAddr] at wordEq
      refine ⟨holFapply f g, refPtrAnnot conf (sptLookup g s.refs), ?_⟩
      rw [← applyEq, ← wordEq] at found
      exact found
end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
