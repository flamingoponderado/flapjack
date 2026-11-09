import Flapjack.Compiler.Backend.Semantics.WordSem.Env

/-! Exception-unwinding facts used by data-to-word correctness. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack

namespace JumpExcSupport

/-- Canonical finite-map witness for the word-semantics state carrier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end JumpExcSupport

/-- Exception unwinding replaces the current locals with the handler frame. -/
@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "jump_exc_locals"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem jumpExcLocals {width : Nat} [NeZero width] {C F : Type}
    (state : WordSemStateFiniteExact width C F) (locals : Spt (WordLocW width)) :
    WordSemStateFiniteExact.jumpExc { state with locals := locals } =
      WordSemStateFiniteExact.jumpExc state := by
  unfold WordSemStateFiniteExact.jumpExc
  by_cases h : state.handler < state.stack.length
  · simp only [h, ↓reduceIte]
  · simp [h]

end Flapjack.Compiler.Backend.DataToWord.Proofs
