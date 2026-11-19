module

public import Flapjack.Compiler.Backend.Semantics.DataSem.State
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

/-- A successful one-variable read determines its individual result. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "get_vars_1_IMP"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem getVars_one_imp {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (x1 : Nat) (v1 : WordLocW width)
    (h : WordSemStateFiniteExact.getVars [x1] s = some [v1]) :
    WordSemStateFiniteExact.getVar x1 s = some v1 := by
  cases a : WordSemStateFiniteExact.getVar x1 s <;>
    simp_all [WordSemStateFiniteExact.getVars]

/-- A successful two-variable read determines both individual results. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "get_vars_2_IMP"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem getVars_two_imp {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (x1 x2 : Nat) (v1 v2 : WordLocW width)
    (h : WordSemStateFiniteExact.getVars [x1, x2] s = some [v1, v2]) :
    WordSemStateFiniteExact.getVar x1 s = some v1 ∧
      WordSemStateFiniteExact.getVar x2 s = some v2 := by
  cases a : WordSemStateFiniteExact.getVar x1 s <;>
    cases b : WordSemStateFiniteExact.getVar x2 s <;>
    simp_all [WordSemStateFiniteExact.getVars]

/-- A successful three-variable read determines all three individual results. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "get_vars_3_IMP"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem getVars_three_imp {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (x1 x2 x3 : Nat) (v1 v2 v3 : WordLocW width)
    (h : WordSemStateFiniteExact.getVars [x1, x2, x3] s = some [v1, v2, v3]) :
    WordSemStateFiniteExact.getVar x1 s = some v1 ∧
      WordSemStateFiniteExact.getVar x2 s = some v2 ∧
      WordSemStateFiniteExact.getVar x3 s = some v3 := by
  cases a : WordSemStateFiniteExact.getVar x1 s <;>
    cases b : WordSemStateFiniteExact.getVar x2 s <;>
    cases c : WordSemStateFiniteExact.getVar x3 s <;>
    simp_all [WordSemStateFiniteExact.getVars]

/-- Successful source-environment reads of a cons split into their two reads. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "get_vars_SOME_IFF_data"]
theorem getVars_some_iff_data {α : Type} (t : Spt α) (x : Nat) (xs : List Nat) (y : α) (ys : List α) :
    (DataSem.getVars [] t = some [] ↔ True) ∧
    (DataSem.getVars (x :: xs) t = some (y :: ys) ↔
      DataSem.getVar x t = some y ∧ DataSem.getVars xs t = some ys) := by
  simp only [DataSem.getVars]
  cases h : DataSem.getVar x t <;> cases h2 : DataSem.getVars xs t <;> simp_all
/-- Successful source-environment reads have exactly the corresponding list shape. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "get_vars_SOME_IFF_data_eq"]
theorem getVars_some_iff_data_eq {α : Type} (t : Spt α) (x : Nat) (xs : List Nat) (z : List α) :
    (DataSem.getVars [] t = some z ↔ z = []) ∧
    (DataSem.getVars (x :: xs) t = some z ↔
      ∃ y ys, z = y :: ys ∧ DataSem.getVar x t = some y ∧ DataSem.getVars xs t = some ys) := by
  cases z <;> simp [DataSem.getVars]
  all_goals cases h : DataSem.getVar x t <;> cases h2 : DataSem.getVars xs t <;> simp_all
  exact ⟨fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩, fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩⟩
end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
