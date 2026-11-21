module

public import Flapjack.Compiler.Backend.Semantics.WordSem.Accessors
public import Flapjack.Compiler.Backend.DataToWord.Variables
@[expose] public section

/-! Register lookup facts for data-to-word assignment correctness. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord

namespace GetVarsDeleteWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end GetVarsDeleteWitness

/-- Scratch-register insertions leave adjusted data-variable lookups unchanged. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "get_vars_delete_lemma"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem getVarsDelete {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (x1 x5 x7 x9 : WordLocW width) (names : List Nat) :
    WordSemStateFiniteExact.getVars (names.map adjustVar)
      {s with locals := sptInsert 9 x9 (sptInsert 7 x7 (sptInsert 5 x5 (sptInsert 1 x1 s.locals)))} =
    WordSemStateFiniteExact.getVars (names.map adjustVar) s := by
  induction names with
  | nil => rfl
  | cons x xs ih =>
    have h1 : adjustVar x ≠ 1 := by simp [adjustVar]
    have h5 : adjustVar x ≠ 5 := by simp [adjustVar]; omega
    have h7 : adjustVar x ≠ 7 := by simp [adjustVar]; omega
    have h9 : adjustVar x ≠ 9 := by simp [adjustVar]; omega
    simp [WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar,
      sptLookup_sptInsert_ne, h1, h5, h7, h9, ih]
/-- An option is present exactly when it is equal to some value. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "INTRO_IS_SOME"]
theorem introIsSome {α : Type} (x : Option α) : (∃ v, x = some v) ↔ x.isSome = true := by
  cases x <;> simp

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
