module

public import Flapjack.Compiler.Backend.DataSpace.Proofs.State
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.AdjustedSet
public import Flapjack.Compiler.Backend.WordToStack.Proofs.CallLocalRecovery
public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.StateLaws
public import Flapjack.Misc.Sptree.FromList.Domain

@[expose] public section

/-! Variable and environment facts for data-to-word call simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend

namespace callEnvMap
/-- Canonical target-state roundtrip for word variable reads. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end callEnvMap

/-- A successful data variable read preserves list length. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "get_vars_IMP_LENGTH"]
theorem getVars_imp_length {α : Type} (names : List Nat) (values : List α) (env : Spt α)
    (read : DataSem.getVars names env = some values) : names.length = values.length :=
  (DataSpace.getVars_length names env values read).symm

/-- A successful word variable read preserves list length. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "get_vars_IMP_LENGTH_word"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem wordGetVars_imp_length {width : Nat} [NeZero width] {C F : Type}
    (names : List Nat) (values : List (WordLocW width)) (state : WordSemStateFiniteExact width C F)
    (read : WordSemStateFiniteExact.getVars names state = some values) :
    names.length = values.length :=
  (WordSemStateFiniteExact.getVarsLengthLemma names state values read).symm

/-- The adjusted data index skips the reserved word return location. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "lookup_adjust_var_fromList2"]
theorem lookup_adjustVar_fromList2 {α : Type} (n : Nat) (w : α) (ws : List α) :
    sptLookup (DataToWord.adjustVar n) (sptFromList2 (w :: ws)) = sptLookup n (sptFromList ws) := by
  rw [WordToStackProofs.fromList2Lookup, sptLookupFromList_getElem?]
  simp [DataToWord.adjustVar]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
