module

public import Flapjack.Compiler.Backend.DataToWord.Variables
public import Flapjack.Compiler.Backend.Semantics.WordSem.Env
public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.StateLaws

@[expose] public section

/-! Opening word-semantics variable and sptree lemmas of
`data_to_word_gcProofScript.sml` (lines 116-147). The unqualified `get_var`,
`set_var` and `push_env` of these HOL statements are the `wordSem` ones (see
the typed capture), rendered by `WordSemStateFiniteExact.getVar`, `setVar` and
`pushEnv`; `LN` is `Spt.ln`, `toAList` is `sptToAList` and `adjust_set` is
`adjustSet`. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

open Flapjack Flapjack.Compiler.Backend.DataToWord

namespace VarLemmasWitnesses
/-- Canonical finite-map roundtrip for the word-semantics state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end VarLemmasWitnesses

/-- Exact HOL `get_var_set_var` (`data_to_word_gcProofScript.sml:116-120`); the
HOL free variables are universally quantified. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "get_var_set_var"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem getVar_setVar_same {width : Nat} [NeZero width] {C F : Type} {n : Nat}
    {w : WordLocW width} {s : WordSemStateFiniteExact width C F} :
    WordSemStateFiniteExact.getVar n (WordSemStateFiniteExact.setVar n w s) = some w := by
  simp only [WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar]
  exact sptLookup_sptInsert_same _ _ _

/-- Exact HOL `set_var_set_var` (`data_to_word_gcProofScript.sml:122-127`); the
HOL free variables are universally quantified. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "set_var_set_var"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem setVar_setVar_same {width : Nat} [NeZero width] {C F : Type} {n : Nat}
    {v w : WordLocW width} {s : WordSemStateFiniteExact width C F} :
    WordSemStateFiniteExact.setVar n v (WordSemStateFiniteExact.setVar n w s) =
      WordSemStateFiniteExact.setVar n v s := by
  simp only [WordSemStateFiniteExact.setVar, sptInsert_insert_shadow]

/-- Exact HOL `toAList_LN` (`data_to_word_gcProofScript.sml:129-133`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "toAList_LN"]
theorem toAList_LN {α : Type} : sptToAList (Spt.ln : Spt α) = [] :=
  sptToAList_ln

/-- Exact HOL `adjust_set_LN` (`data_to_word_gcProofScript.sml:135-139`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "adjust_set_LN"]
theorem adjust_set_LN {α : Type} : adjustSet (Spt.ln : Spt α) = Spt.ln := by
  simp [adjustSet]
  rfl

/-- Exact HOL `push_env_termdep` (`data_to_word_gcProofScript.sml:141-147`);
the HOL free variables are universally quantified. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "push_env_termdep"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem pushEnv_termdep {width : Nat} [NeZero width] {C F : Type}
    {y : Spt (WordLocW width) × Spt (WordLocW width)}
    {opt : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat)}
    {t : WordSemStateFiniteExact width C F} :
    (WordSemStateFiniteExact.pushEnv y opt t).termdep = t.termdep := by
  cases opt with
  | none => rfl
  | some x => obtain ⟨_, _, _, _⟩ := x; rfl

/-- Exact HOL `get_var_set_var_thm` (`data_to_word_gcProofScript.sml:8072-8076`);
the HOL free variables are universally quantified. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "get_var_set_var_thm"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem getVar_setVar_thm {width : Nat} [NeZero width] {C F : Type} {n m : Nat}
    {x : WordLocW width} {y : WordSemStateFiniteExact width C F} :
    WordSemStateFiniteExact.getVar n (WordSemStateFiniteExact.setVar m x y) =
      if n = m then some x else WordSemStateFiniteExact.getVar n y :=
  WordSemStateFiniteExact.getVarSetVar n m x y

/-- Exact HOL `insert_insert_3_1` (`data_to_word_gcProofScript.sml:8017-8021`);
the HOL free variables are universally quantified. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "insert_insert_3_1"]
theorem insert_insert_3_1 {α : Type} {x y : α} {t : Spt α} :
    sptInsert 3 x (sptInsert 1 y t) = sptInsert 1 y (sptInsert 3 x t) :=
  sptInsert_swap 3 1 x y t (by decide)

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
