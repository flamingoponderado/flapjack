module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.StoreEach
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateInsert

@[expose] public section

/-! Variable reads used in reference allocation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord

namespace ReferenceReadWitness
/-- Canonical word-state map roundtrip. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
/-- Canonical carrier witness for relation-qualified word-state fields. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end ReferenceReadWitness

/-- An odd scratch register cannot affect adjusted source-variable reads. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "get_vars_adjust_var"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem getVarsAdjustVar {width : Nat} [NeZero width] {C F : Type}
    (args : List Nat) (t : WordSemStateFiniteExact width C F)
    (locals : Spt (WordLocW width)) (k : Nat) (w : WordLocW width) (odd : k % 2 = 1) :
    WordSemStateFiniteExact.getVars (args.map adjustVar) {t with locals := sptInsert k w locals} =
      WordSemStateFiniteExact.getVars (args.map adjustVar) {t with locals := locals} := by
  induction args with
  | nil => rfl
  | cons head tail ih =>
    have different : adjustVar head ≠ k := by simp [adjustVar] at *; omega
    simp [WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar,
      sptLookup_sptInsert_ne k (adjustVar head) w locals different, ih]

/-- Variable reads depend on locals and are unaffected by replacing the store. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "get_vars_with_store"
  (fmap_as_finite_support_relation := [replacement, WordSemStateFiniteExact.fpRegs, WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem getVarsWithStore {width : Nat} [NeZero width] {C F : Type}
    (args : List Nat) (t : WordSemStateFiniteExact width C F)
    (replacement : HolFiniteMapExact WordStoreHOL (WordLocW width)) :
    WordSemStateFiniteExact.getVars args {t with locals := t.locals, store := replacement} =
      WordSemStateFiniteExact.getVars args t := by
  induction args with
  | nil => rfl
  | cons head tail ih => simp [WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, ih]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
