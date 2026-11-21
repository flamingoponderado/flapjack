module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateRelation

@[expose] public section

/-! Simplification of the data-to-word state relation under a combined
locals and space-safety update (`data_to_wordProofScript.sml` lines 37-43). -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

namespace reviewedStateRelWithLocalsSfsMap
/-- Canonical roundtrip for the target state used by this HOL port. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end reviewedStateRelWithLocalsSfsMap

/-- The relation does not observe the source `safe_for_space` flag. -/
@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "state_rel_with_locals_sfs"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem stateRel_withLocalsSfs {width : Nat} [NeZero width] {C F : Type}
    (c : Config) (l1 l2 : Nat) (x : Flapjack.Compiler.Backend.DataSem.State C F)
    (l : Spt Flapjack.Compiler.Backend.DataSem.Value) (m : Bool)
    (r : WordSemStateFiniteExact width C F)
    (t : Option (List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width))) (locs : List (Nat × Nat)) :
    stateRel c l1 l2 { x with locals := l, safeForSpace := m } r t locs ↔
      stateRel c l1 l2 { x with locals := l } r t locs :=
  Iff.rfl

end Flapjack.Compiler.Backend.DataToWord.Proofs
