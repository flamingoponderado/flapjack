module

public import Flapjack.Compiler.Backend.Semantics.WordSem.Accessors

@[expose] public section

/-! A singleton read from the word semantics produces exactly one value. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

namespace GetVarsSingleWitnesses

/-- Canonical finite-map roundtrip for the word-semantics state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end GetVarsSingleWitnesses

/-- A successful singleton variable read has a singleton result. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "get_vars_sing"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem getVars_sing {width : Nat} [NeZero width] {C F : Type}
    (n : Nat) (t : WordSemStateFiniteExact width C F) (x : List (WordLocW width)) :
    WordSemStateFiniteExact.getVars [n] t = some x ↔
      ∃ x1, WordSemStateFiniteExact.getVars [n] t = some [x1] ∧ x = [x1] := by
  cases h : WordSemStateFiniteExact.getVar n t <;>
    simp [WordSemStateFiniteExact.getVars, h, eq_comm]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
