module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CallEnv
public import Flapjack.Compiler.Backend.Semantics.DataProps.Variables

@[expose] public section

/-! End-of-list variable reads used by indirect calls. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend

namespace getVarsSnocMap
/-- Canonical target-state roundtrip for word variable reads. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end getVarsSnocMap

/-- A successful read of a final data variable splits into its two reads. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "data_get_vars_SNOC_IMP" 5196]
theorem dataGetVars_snoc {α : Type} (names : List Nat) (values : List α) (last : Nat) (env : Spt α)
    (read : DataSem.getVars (names ++ [last]) env = some values) :
    ∃ lastValue prefixValues, values = prefixValues ++ [lastValue] ∧
      DataSem.getVar last env = some lastValue ∧ DataSem.getVars names env = some prefixValues := by
  rw [DataProps.getVars_append] at read
  cases prefixEq : DataSem.getVars names env with
  | none => simp [prefixEq] at read
  | some prefixValues =>
    cases value : DataSem.getVar last env with
    | none => simp [prefixEq, DataSem.getVars, value] at read
    | some lastValue =>
      simp [prefixEq, DataSem.getVars, value] at read
      exact ⟨lastValue, prefixValues, read.symm, rfl, rfl⟩

/-- Word reads and generic sparse-environment reads use the same lookup. -/
private theorem wordGetVars_eq_data {width : Nat} [NeZero width] {C F : Type}
    (names : List Nat) (state : WordSemStateFiniteExact width C F) :
    WordSemStateFiniteExact.getVars names state = DataSem.getVars names state.locals := by
  induction names with
  | nil => rfl
  | cons name names ih =>
    simp only [WordSemStateFiniteExact.getVars, DataSem.getVars, WordSemStateFiniteExact.getVar,
      DataSem.getVar, ih]
    cases sptLookup name state.locals <;> cases DataSem.getVars names state.locals <;> rfl

/-- A successful read of a final word variable splits into its two reads. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_get_vars_SNOC_IMP" 5207
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem wordGetVars_snoc {width : Nat} [NeZero width] {C F : Type}
    (names : List Nat) (values : List (WordLocW width)) (last : Nat)
    (state : WordSemStateFiniteExact width C F)
    (read : WordSemStateFiniteExact.getVars (names ++ [last]) state = some values) :
    ∃ lastValue prefixValues, values = prefixValues ++ [lastValue] ∧
      WordSemStateFiniteExact.getVar last state = some lastValue ∧
      WordSemStateFiniteExact.getVars names state = some prefixValues := by
  rw [wordGetVars_eq_data] at read
  obtain ⟨lastValue, prefixValues, valuesEq, lastRead, prefixRead⟩ :=
    dataGetVars_snoc names values last state.locals read
  exact ⟨lastValue, prefixValues, valuesEq, lastRead, by simpa [wordGetVars_eq_data] using prefixRead⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
