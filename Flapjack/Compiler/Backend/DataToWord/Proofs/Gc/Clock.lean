module

public import Flapjack.Compiler.Backend.Semantics.DataSem.State
public import Flapjack.Compiler.Backend.Semantics.WordSem.Accessors

@[expose] public section

/-! Clock identities used in the data-to-word allocation proof. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

/-- Incrementing and then decrementing either evaluator's clock restores its state. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "dec_clock_inc_clock"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem decClockIncClock {width : Nat} [NeZero width] {C F D G : Type}
    (source : DataSem.State C F) (target : WordSemStateFiniteExact width D G) :
    DataSem.decClock { source with clock := source.clock + 1 } = source ∧
    WordSemStateFiniteExact.decClock { target with clock := target.clock + 1 } = target := by
  simp [DataSem.decClock, WordSemStateFiniteExact.decClock]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
