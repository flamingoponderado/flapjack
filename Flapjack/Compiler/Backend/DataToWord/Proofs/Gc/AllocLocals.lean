module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CutOdd
public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.LocalsRel

@[expose] public section

/-! Allocation ignores a temporary outside the adjusted live sets. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

namespace AllocLocalsWitnesses
/-- Canonical finite-map roundtrip for the word-semantics state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end AllocLocalsWitnesses

/-- Inserting temporary local 1 does not change allocation on adjusted sets. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "alloc_locals_insert_1"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem alloc_locals_insert_one {width : Nat} [NeZero width] {C F α : Type}
    (k : BitVec width) (names : Spt α) (t : WordSemStateFiniteExact width C F)
    (w : WordLocW width) :
    WordSemStateFiniteExact.alloc k (adjustSets names) {t with locals := sptInsert 1 w t.locals} =
      WordSemStateFiniteExact.alloc k (adjustSets names) t := by
  apply WordSemStateFiniteExact.alloc_withLocals
  exact cutEnvs_adjustSets_insertOdd names t.locals 1 w (by decide)

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
