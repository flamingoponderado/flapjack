module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateRelation
@[expose] public section

/-! Timestamp availability under the data-to-word state relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

namespace StateTstampsWitnesses
/-- Canonical finite-map roundtrip for the word-semantics state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end StateTstampsWitnesses

/-- The related source state has a next timestamp. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "state_rel_IMP_tstamps"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem stateRel_imp_tstamps {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (l1 l2 : Nat) (source : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F)
    (values : Option (List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width))) (locs : List (Nat × Nat))
    (related : stateRel conf l1 l2 source target values locs) :
    ∃ next, source.tstamps = some next := by
  exact Option.isSome_iff_exists.mp related.2.2.2.2.2.2.2.2.1
end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
