module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateRelation
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.StackPermute
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.WordMlInvLookup
@[expose] public section

/-! Related word representation of data blocks. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

namespace blockLookupMap
/-- Canonical target-state finite-map roundtrip. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end blockLookupMap

/-- A related data block local is represented by a word, not a location. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "state_rel_get_var_Block"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem stateRel_getVar_block {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (s : Flapjack.Compiler.Backend.DataSem.State C F)
    (t : WordSemStateFiniteExact width C F) (v : Option (List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)))
    (locs : List (Nat × Nat)) (n ts tag : Nat) (vs : List Flapjack.Compiler.Backend.DataSem.Value)
    (premises : stateRel conf l1 l2 s t v locs ∧ DataSem.getVar n s.locals = some (.block ts tag vs)) :
    ∃ w, WordSemStateFiniteExact.getVar (DataToWord.adjustVar n) t = some (.word w) := by
  obtain ⟨related, sourceRead⟩ := premises
  obtain ⟨word, targetRead⟩ := stateRel_getVar conf l1 l2 s t v locs n (.block ts tag vs) related sourceRead
  rcases related with ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift,
    htstamp, hglobal, hzero, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, hmem⟩
  obtain ⟨heap, limit, a, sp, sp1, gens, hstore, hinv, hbound, hspace⟩ := hmem
  have singleton : wordMlInv (heap, t.be, a, sp, sp1, gens) limit (holThe s.tstamps) conf s.refs
      [(.block ts tag vs, word)] := by
    apply wordMlInv_rearrange heap t.be a sp sp1 gens limit (holThe s.tstamps) conf s.refs _ _ ?_ hinv
    intro pair member
    simp only [List.mem_singleton] at member
    subst pair
    have inJoin : (.block ts tag vs, word) ∈ joinEnv s.locals (sptToAList (sptInter t.locals (DataToWord.adjustSet s.locals))) := by
      simp only [joinEnv, List.mem_map, List.mem_filter]
      have sourceFound : sptLookup n s.locals = some (.block ts tag vs) := sourceRead
      have targetFound : sptLookup (DataToWord.adjustVar n) t.locals = some word := targetRead
      have adjusted : sptLookup (DataToWord.adjustVar n) (DataToWord.adjustSet s.locals) = some () := by
        rw [lookup_adjustSet_map, sourceFound]
        rfl
      refine ⟨(DataToWord.adjustVar n, word), ⟨?_, ?_⟩, ?_⟩
      · apply (sptMemToAList _ _ _).mpr
        rw [sptLookup_sptInterCases, targetFound, adjusted]
      · simp [DataToWord.adjustVar]
      · simp [DataToWord.adjustVar, sourceFound, holThe]
    simp [inJoin]
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
      cases value0 <;> simp only [wordAddr] at wordEq <;> subst word <;> exact ⟨_, targetRead⟩
end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
