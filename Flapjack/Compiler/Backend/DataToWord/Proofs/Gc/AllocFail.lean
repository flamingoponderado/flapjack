module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.AllocDimword
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.AllocLemma
@[expose] public section

/-! Allocation failure at the all-ones sentinel. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.BackendProps Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

namespace AllocFailWitnesses
/-- Canonical finite-map roundtrip for the target state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end AllocFailWitnesses

/-- Allocating the all-ones sentinel fails while preserving the FFI and stack bound. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "alloc_fail"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem allocFail {width : Nat} [NeZero width] {C F : Type} (conf : Flapjack.Compiler.Backend.DataToWord.Config) (l1 l2 : Nat)
    (source : Flapjack.Compiler.Backend.DataSem.State C F) (target result : WordSemStateFiniteExact width C F)
    (locs : List (Nat × Nat)) (names : NumSet) (cutData : Spt Flapjack.Compiler.Backend.DataSem.Value)
    (q : Option (WordSemResult width))
    (premises : goodDimindex width ∧ stateRel conf l1 l2 source target none locs ∧
      DataSem.cutEnv names source.locals = some cutData ∧
      WordSemStateFiniteExact.alloc (-1) (adjustSets names) target = (q, result)) :
    (q = some .notEnoughSpace → result.ffi = source.ffi ∧ optionLe result.stackMax source.stackMax) ∧
      q = some .notEnoughSpace := by
  obtain ⟨good, related, cut, run⟩ := premises
  have sentinel := allocSize_dimword (width := width) good
  have runSize : WordSemStateFiniteExact.alloc (gcAllocSize (2 ^ width)) (adjustSets names) target = (q, result) := by
    simpa [sentinel] using run
  have facts := allocLemma conf l1 l2 source target result locs names cutData (2 ^ width) q ⟨related, cut, runSize⟩
  have bad : q = some .notEnoughSpace := by
    by_contra h
    exact (facts.2 h).2.1 sentinel
  exact ⟨fun h => ⟨(facts.1 h).1, (facts.1 h).2.1⟩, bad⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
