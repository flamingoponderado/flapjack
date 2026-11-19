module

public import Flapjack.Compiler.Backend.Semantics.WordSem.Accessors
public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.StateConst

@[expose] public section

/-! Variable-list lookup properties used by the data-to-word GC proof. -/
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

/-- Reading variables is unaffected by decrementing the termination depth. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "get_vars_termdep"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec), simp]
theorem getVars_termdep {width : Nat} [NeZero width] {C F : Type}
    (t : WordSemStateFiniteExact width C F) :
    ∀ xs : List Nat, WordSemStateFiniteExact.getVars xs {t with termdep := t.termdep - 1} =
      WordSemStateFiniteExact.getVars xs t := by
  exact WordSemStateFiniteExact.getVars_congr t {t with termdep := t.termdep - 1} rfl

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
